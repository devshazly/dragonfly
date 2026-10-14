// Copyright 2026, DragonflyDB authors.  All rights reserved.
// See LICENSE for licensing terms.
//

#include "server/journal/aof_chain_reader.h"

#include <absl/strings/numbers.h>
#include <absl/strings/str_cat.h>
#include <absl/strings/strip.h>
#include <fcntl.h>

#include <algorithm>
#include <cstring>

#include "base/logging.h"
#include "io/file_util.h"
#include "server/error.h"
#include "server/journal/aof_segment_writer.h"
#include "util/fibers/uring_file.h"

namespace dfly {

using namespace std;
using util::fb2::OpenLinux;

namespace {

constexpr size_t kMaxBlockBytes = kAofBlockHeaderSize + kAofBlockBytes;

}  // namespace

AofChainReader::AofChainReader(string dir, uint32_t shard_id, uint32_t shard_count)
    : dir_(std::move(dir)), shard_id_(shard_id), shard_count_(shard_count) {
}

AofChainReader::~AofChainReader() = default;

string AofChainReader::SegmentPath(uint64_t seq) const {
  return absl::StrCat(dir_, "/", AofSegmentWriter::SegmentName(shard_id_, seq));
}

error_code AofChainReader::Open() {
  auto files = io::StatFiles(absl::StrCat(dir_, "/appendonly-", shard_id_, "-*.aof"));
  if (!files)
    return files.error();

  // Collect the shard's segments; the seq is in the file name.
  string prefix = absl::StrCat("appendonly-", shard_id_, "-");
  for (const auto& file : *files) {
    string_view seq_str = string_view(file.name).substr(file.name.rfind('/') + 1);
    uint64_t seq = 0;
    if (!absl::ConsumePrefix(&seq_str, prefix) || !absl::ConsumeSuffix(&seq_str, ".aof") ||
        !absl::SimpleAtoi(seq_str, &seq)) {
      return make_error_code(errc::illegal_byte_sequence);
    }
    segment_chain_.push_back({seq, file.size, 0, nullptr});
  }
  if (segment_chain_.empty())
    return make_error_code(errc::no_such_file_or_directory);

  // The log runs through the segments in seq order.
  sort(segment_chain_.begin(), segment_chain_.end(),
       [](const Segment& a, const Segment& b) { return a.seq < b.seq; });

  for (size_t i = 0; i < segment_chain_.size(); ++i) {
    Segment& seg = segment_chain_[i];
    // A missing seq or a file without a full header.
    if (seg.seq != segment_chain_.front().seq + i || seg.size < kAofSegmentHeaderSize)
      return make_error_code(errc::illegal_byte_sequence);

    auto file = OpenLinux(SegmentPath(seg.seq), O_RDONLY, 0);
    if (!file)
      return file.error();
    seg.file = std::move(*file);
    string hdr_bytes(kAofSegmentHeaderSize, '\0');
    iovec v{hdr_bytes.data(), hdr_bytes.size()};
    RETURN_ON_ERR(seg.file->Read(&v, 1, 0, 0));

    // The header must be valid and match the file's name and the chain.
    auto hdr = DecodeAofSegmentHeader(hdr_bytes);
    if (!hdr || hdr->shard_id != shard_id_ || hdr->shard_count != shard_count_ ||
        hdr->seq != seg.seq) {
      return make_error_code(errc::illegal_byte_sequence);
    }
    // Seeds the CRCs of the segment's blocks.
    seg.uid = hdr->segment_uid;
  }
  return {};
}

error_code AofChainReader::ReadBlock() {
  const Segment& seg = segment_chain_[read_seg_id_];
  // Up to one maximum-size block; a smaller block leaves the next block's bytes for the next read.
  buf_.resize(min<uint64_t>(kMaxBlockBytes, seg.size - offset_));
  iovec v{buf_.data(), buf_.size()};
  RETURN_ON_ERR(seg.file->Read(&v, 1, offset_, 0));
  // Bad CRC or size: a torn write or a hole.
  auto hdr = DecodeAofBlock(buf_, seg.uid);
  if (!hdr) {
    Finish(true);
    return {};
  }
  // A block that does not follow the previous one: a stale block past the end of the log.
  bool lsn_break = prev_block_ && hdr->first_lsn != prev_block_->first_lsn + prev_block_->n_records;
  bool continues = hdr->flags & kStartsWithContinuation;
  if (lsn_break || continues != EndsMidRecord()) {
    Finish(true);
    return {};
  }

  prev_block_ = *hdr;
  offset_ += hdr->total_block_bytes;
  // Every valid block is handed out right away, so memory stays bounded by one block. A record
  // that continues in the next block is buffered by JournalReader until it completes.
  // TODO: the end of the log moves only at blocks ending at a record boundary. If the log ends
  // inside a record, the complete records before it in the same blocks are not counted. Keep
  // those blocks instead and abandon only the incomplete record: the resumed segment's header
  // marks it abandoned, and replay resets its JournalReader at that segment boundary.
  if (!EndsMidRecord()) {
    end_seg_id_ = read_seg_id_;
    end_offset_ = offset_;
    last_lsn_ = hdr->first_lsn + hdr->n_records - 1;
  }
  // Hand out the payload, without the block header.
  pending_ =
      string_view(buf_).substr(kAofBlockHeaderSize, hdr->total_block_bytes - kAofBlockHeaderSize);
  return {};
}

io::Result<size_t> AofChainReader::ReadSome(const iovec* v, uint32_t len) {
  while (pending_.empty()) {
    if (end_ != End::kNotYet) {
      if (end_ == End::kTailTorn)
        return nonstd::make_unexpected(make_error_code(errc::illegal_byte_sequence));
      return 0;
    }
    // Reached the end of the current segment.
    if (offset_ == segment_chain_[read_seg_id_].size) {
      // A record cut at the end of the segment.
      if (EndsMidRecord()) {
        Finish(true);
        continue;
      }
      // Read past the last segment: the log ends cleanly.
      if (++read_seg_id_ == segment_chain_.size()) {
        Finish(false);
        continue;
      }
      // Continue with the next segment, after its header. The previous one ended cleanly, so the
      // log reaches at least this point.
      offset_ = kAofSegmentHeaderSize;
      end_seg_id_ = read_seg_id_;
      end_offset_ = offset_;
      continue;
    }
    if (error_code ec = ReadBlock(); ec)
      return nonstd::make_unexpected(ec);
  }

  // Copy as much of the current payload as fits in v.
  size_t copied = 0;
  for (uint32_t i = 0; i < len && !pending_.empty(); ++i) {
    size_t n = min(v[i].iov_len, pending_.size());
    memcpy(v[i].iov_base, pending_.data(), n);
    pending_.remove_prefix(n);
    copied += n;
  }
  return copied;
}

void AofChainReader::Finish(bool torn) {
  end_ = torn ? End::kTailTorn : End::kTailReached;
  discarded_bytes_ = segment_chain_[end_seg_id_].size - end_offset_;
  for (size_t i = end_seg_id_ + 1; i < segment_chain_.size(); ++i)
    discarded_bytes_ += segment_chain_[i].size;
  LOG_IF(WARNING, torn) << "AOF shard " << shard_id_ << ": damaged tail of " << discarded_bytes_
                        << " bytes after lsn " << last_lsn_;
}

}  // namespace dfly
