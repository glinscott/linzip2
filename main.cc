#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cmath>
#include <cstdlib>
#include <cstdint>
#include <string>
#include <vector>

////////////
// Utilities

constexpr int kDebugLevel = 2;

#define CHECK(cond) do{if(!(cond)){fprintf(stderr,"%s:%d CHECK %s\n", __FILE__, __LINE__, #cond);exit(1);}}while(0);
#define LOGV(level, s, ...) do{if(level<=kDebugLevel) fprintf(stderr, s, ##__VA_ARGS__);}while(0);

struct Timer {
  Timer() : time_(std::chrono::high_resolution_clock::now()) {}
  double elapsed() const { return std::chrono::duration<double, std::milli>(std::chrono::high_resolution_clock::now()-time_).count(); }
  std::chrono::high_resolution_clock::time_point time_;
};

bool FLAG_test = false;
int FLAG_level = 0;
int FLAG_window_size = 18;
int FLAG_max_matches = 8;

////////////

constexpr int64_t kMaxChunkSize = 1 << 18; // 256k

std::string toBinary(int v, int size) {
  std::string result;
  for (int j = 0; j < size; ++j) {
    result += ((v>>(size-j-1))&1) ? "1" : "0";
  }
  return result;
}

int log2(int v) {
  if (v > 0) {
    return 31 - __builtin_clz(v);
  }
  return 0;
}

class BitReader {
public:
  BitReader(uint8_t* buffer, uint8_t* end)
    : current_(buffer),
      end_(end) {
    refill();
  }

  // offset adjusts the stream position before reading any bits.  This allows
  // the BitReader to resume a "backward" stream, which doesn't have to end on
  // a byte boundary.
  BitReader(uint8_t* buffer, uint8_t* end, int offset)
    : current_(buffer),
      end_(end) {
    position_ += offset;
    refill();
  }

  int readBit() {
    int r = bits_ >> 31;
    bits_ <<= 1;
    ++position_;
    return r;
  }

  int readBits(int n) {
    int r = bits_ >> (32 - n);
    bits_ <<= n;
    position_ += n;
    return r;
  }

  void refill() {
    while (position_ >= 0) {
      bits_ |= (current_ < end_ ? *current_ : 0) << position_;
      position_ -= 8;
      ++current_;
    }
  }

  void byteAlign() {
    int extra_bits = position_ & 7;
    if (extra_bits) {
      readBits(8 - extra_bits);
    }
  }

  uint8_t* current() const { return current_; }
  uint8_t* end() const { return end_; }
  uint32_t bits() const { return bits_; }
  int position() const { return position_; }

  // Actual location we have read up to in the byte stream.
  uint8_t* cursor() const {
    return current_ - ((24 - position_) / 8);
  }

private:
  uint8_t* current_;
  uint8_t* end_;
  uint32_t bits_ = 0;
  int position_ = 24;
};

class BitWriter {
public:
  BitWriter(uint8_t* buffer)
    : start_(buffer),
      current_(buffer) {
  }

  void writeBit(int v) {
    bits_ = (bits_ << 1) | v;
    ++position_;
    if (position_ >= 8) {
      flush();
    }
  }

  void writeBits(int v, int n) {
    bits_ = (bits_ << n) | v;
    position_ += n;
    if (position_ >= 8) {
      flush();
    }
  }

  int64_t finish() {
    flush();
    CHECK(position_ >= 0 && position_ < 8);
    if (position_ > 0) {
      // Final byte is a bit tricky.  Handle it specially.
      *current_ = (bits_ & ((1 << position_) - 1)) << (8 - position_);
      ++current_;
      position_ = 0;
    }
    return current_ - start_;
  }

private:
  void flush() {
    while (position_ >= 8) {
      position_ -= 8;
      *current_ = (bits_ >> position_) & 0xFF;
      ++current_;
    }
  }

private:
  uint8_t* start_;
  uint8_t* current_;
  uint32_t bits_ = 0;
  int position_ = 0;
};

class ReverseBitWriter {
public:
  // ReverseBitWriter starts writing from buffer (end-exclusive) going downwards
  // in memory, instead of going forward.  Eg. written data is from:
  // [buffer - finish(), buffer)
  ReverseBitWriter(uint8_t* buffer)
    : start_(buffer),
      current_(buffer) {
  }

  int position() const { return position_; }

  void writeBits(uint32_t v, int n) {
    bits_ = (bits_ >> n) | (v << (32 - n));
    position_ += n;
    if (position_ >= 8) {
      flush();
    }
  }

  int64_t finish() {
    CHECK(position_ >= 0 && position_ < 8);
    if (position_ > 0) {
      // Final byte is a bit tricky.  Handle it specially.
      --current_;
      *current_ = bits_ >> (32 - position_);
      bits_ = 0;
    }
    return start_ - current_;
  }

private:
  void flush() {
    *reinterpret_cast<uint32_t*>(current_ - 4) = __builtin_bswap32(bits_ >> (32 - position_));
    current_ -= position_ >> 3;
    position_ &= 7;
  }

private:
  uint8_t* start_;
  uint8_t* current_;
  uint32_t bits_ = 0;
  int position_ = 0;
};

const int kMaxHuffCodeLength = 11;

class HuffmanEncoder {
private:
  struct Node {
    int freq;
    int symbol;
    Node* l;
    Node* r;
  };

  struct Comparator {
    bool operator()(const Node* l, const Node* r) {
      return l->freq > r->freq;
    }
  };

public:
  HuffmanEncoder(uint8_t* buffer, int max_symbols = 256)
    : writer_(buffer),
      max_symbols_(max_symbols) {
    for (int i = 0; i < max_symbols_; ++i) {
      nodes_[i].symbol = i;
      nodes_[i].freq = 0;
    }
  }

  BitWriter& writer() { return writer_; }

  void scan(int symbol) {
    ++nodes_[symbol].freq;
  }

  void buildTable() {
    // Coalesce used symbols, and add to heap
    Node* q[256];
    int num_symbols = 0;
    for (int i = 0; i < max_symbols_; ++i) {
      if (nodes_[i].freq) {
        nodes_[num_symbols] = nodes_[i];
        q[num_symbols] = &nodes_[num_symbols];
        ++num_symbols;
      }
    }

    Comparator c;
    std::make_heap(&q[0], &q[num_symbols], c);

    // Build Huffman tree
    for (int i = num_symbols; i > 1; --i) {
      Node* n1 = q[0];
      std::pop_heap(&q[0], &q[i], c);
      Node* n2 = q[0];
      std::pop_heap(&q[0], &q[i-1], c);

      Node* parent = &nodes_[num_symbols+i];
      parent->freq = n1->freq + n2->freq;
      parent->symbol = -1;
      parent->l = n2;
      parent->r = n1;
      q[i-2] = parent;
      std::push_heap(&q[0], &q[i-1], c);
    }

    // Label the distances from the root for the leafs
    walk(q[0], num_symbols == 1 ? 1 : 0);

    // Sort leaf nodes into level order.  This is required
    // for both length limiting and writing the table.
    std::sort(&nodes_[0], &nodes_[num_symbols], [](const Node& l, const Node& r){return l.freq < r.freq;});

    limitLength(num_symbols);
    writeTable(num_symbols);
    buildCodes(num_symbols);
  }

  void encode(int symbol) {
    writer_.writeBits(code_[symbol], length_[symbol]);
  }

  int64_t finish() {
    return writer_.finish();
  }

private:
  void writeTable(int num_symbols) {
    const int kSymBits = log2(max_symbols_);
    writer_.writeBits(num_symbols - 1, kSymBits);

    for (int i = 0; i < num_symbols; ++i) {
      writer_.writeBits(nodes_[i].symbol, kSymBits);
      writer_.writeBits(nodes_[i].freq - 1, 4);
    }

    // Byte align after the table
    writer_.finish();
  }

  void buildCodes(int num_symbols) {
    int code = 0;
    int last_level = -1;
    LOGV(2, "Write num_symbols %d\n", num_symbols);
    for (int i = 0; i < num_symbols; ++i) {
      // Build the binary representation.
      int level = nodes_[i].freq;
      if (last_level != level) {
        if (last_level != -1) {
          ++code;
          code <<= (level - last_level);
        }
        last_level = level;
      } else {
        ++code;
      }

      int symbol = nodes_[i].symbol;
      length_[symbol] = level;
      code_[symbol] = code;

      LOGV(2, "code:%s hex:%x level:%d symbol:%d\n", toBinary(code, level).c_str(), code, level, symbol);
    }
  }

  void limitLength(int num_symbols) {
    // Limit the maximum code length
    int k = 0;
    int maxk = (1 << kMaxHuffCodeLength) - 1;
    for (int i = num_symbols - 1; i >= 0; --i) {
      nodes_[i].freq = std::min(nodes_[i].freq, kMaxHuffCodeLength);
      k += 1 << (kMaxHuffCodeLength - nodes_[i].freq);
    }
    LOGV(3, "k before: %.6lf\n", k / double(maxk));
    for (int i = num_symbols - 1; i >= 0 && k > maxk; --i) {
      while (nodes_[i].freq < kMaxHuffCodeLength) {
        ++nodes_[i].freq;
        k -= 1 << (kMaxHuffCodeLength - nodes_[i].freq);
      }
    }
    LOGV(3, "k pass1: %.6lf\n", k / double(maxk));
    for (int i = 0; i < num_symbols; ++i) {
      while (k + (1 << (kMaxHuffCodeLength - nodes_[i].freq)) <= maxk) {
        k += 1 << (kMaxHuffCodeLength - nodes_[i].freq);
        --nodes_[i].freq;
      }
    }
    LOGV(3, "k pass2: %x, %x\n", k, maxk);
  }

  void walk(Node* n, int level) {
    if (n->symbol != -1) {
      n->freq = level;
      return;
    }

    walk(n->l, level + 1);
    walk(n->r, level + 1);
  }

  BitWriter writer_;
  int max_symbols_;

  Node nodes_[512];

  uint8_t length_[256];
  int code_[256];
};

class HuffmanDecoder {
public:
  HuffmanDecoder(uint8_t* buffer, uint8_t* end, int sym_bits = 8)
    : br_(buffer, end),
      sym_bits_(sym_bits) {
  }

  BitReader& br() { return br_; }

  void readTable() {
    br_.refill();
    num_symbols_ = br_.readBits(sym_bits_) + 1;

    CHECK(num_symbols_ <= kMaxSymbols);

    for (int i = 0; i < num_symbols_; ++i) {
      br_.refill();
      int symbol = br_.readBits(sym_bits_);
      int codelen = br_.readBits(4) + 1;
      LOGV(2, "sym:%d len:%d\n", symbol, codelen);

      ++codelen_count_[codelen];
      symbol_[i] = symbol;
      min_codelen_ = std::min(min_codelen_, codelen);
      max_codelen_ = std::max(max_codelen_, codelen);
    }
    LOGV(1, "num_sym %d codelen(min:%d, max:%d)\n", num_symbols_, min_codelen_, max_codelen_);

    // Ensure we catch up to be byte aligned.
    br_.byteAlign();

    assignCodes();
  }

  void decode(uint8_t* output, uint8_t* output_end) {
    uint8_t* src = br_.cursor();
    uint8_t* src_end = br_.end();
    int position = 24;
    uint32_t bits = 0;

    for (;;) {
      while (position >= 0) {
        bits |= (src < src_end ? *src++ : 0) << position;
        position -= 8;
      }
      int n = bits >> (32 - max_codelen_);
      int len = bits_to_len_[n];
      *output++ = bits_to_sym_[n];
      if (output >= output_end) {
        break;
      }
      bits <<= len;
      position += len;
    }
  }

  uint8_t decodeOne() {
    br_.refill();
    int n = br_.bits() >> (32 - max_codelen_);
    int len = bits_to_len_[n];
    br_.readBits(len);
    return bits_to_sym_[n];
  }

  static const int kMaxSymbols = 256;

private:
  void assignCodes() {
    int p = 0;
    uint8_t* cursym = &symbol_[0];
    for (int i = min_codelen_; i <= max_codelen_; ++i) {
      int n = codelen_count_[i];
      if (n) {
        int shift = max_codelen_ - i;
        memset(bits_to_len_ + p, i, n << shift);
        int m = 1 << shift;
        do {
          memset(bits_to_sym_ + p, *cursym++, m);
          p += m;
        } while(--n);
      }
    }
  }

  BitReader br_;
  int sym_bits_;
  int num_symbols_;
  int min_codelen_ = 255;
  int max_codelen_ = 0;
  int codelen_count_[17] = {0};

  uint8_t symbol_[256];
  uint8_t bits_to_sym_[0x800];
  uint8_t bits_to_len_[0x800];
};

int64_t huffmanCompress(uint8_t* buf, int64_t len, uint8_t* out) {
  uint8_t* out_start = out;
  int64_t chunk_size = kMaxChunkSize;
  for (int64_t start = 0; start < len; start += chunk_size) {
    int64_t remaining = std::min(chunk_size, len - start);
    uint8_t* marker = out;
    out += 3;

    HuffmanEncoder encoder(out);
    for (int64_t i = 0; i < remaining; ++i) {
      encoder.scan(buf[i]);
    }
    encoder.buildTable();
    for (int64_t i = 0; i < remaining; ++i) {
      encoder.encode(buf[i]);
    }
    int64_t chunk_written = encoder.finish();
    marker[0] = chunk_written & 0xff;
    marker[1] = (chunk_written >> 8) & 0xff;
    marker[2] = (chunk_written >> 16) & 0xff;

    buf += remaining;
    out += chunk_written;
  }
  return out - out_start;
}

void huffmanDecompress(uint8_t* buf, int64_t len, uint8_t* out, int64_t out_len) {
  int64_t read = 0;
  int64_t chunk_size = kMaxChunkSize;
  uint8_t* buf_end = buf + len;
  while (buf < buf_end) {
    int compressed_size = buf[0] | (buf[1] << 8) | (buf[2] << 16);
    buf += 3;

    HuffmanDecoder decoder(buf, buf + compressed_size);
    decoder.readTable();
    decoder.decode(out, out + std::min(chunk_size, out_len));

    buf += compressed_size;
    out += chunk_size;
    out_len -= chunk_size;
  }
}

void sortSymbols(int state_len, int num_symbols, int* freq, int* sorted_symbols) {
  // http://fastcompression.blogspot.com/2014/02/fse-distributing-symbol-values.html
  // http://cbloomrants.blogspot.com/2014/02/02-06-14-understanding-ans-8.html
  std::pair<float, int> sorted[state_len];
  int at = 0;
  for (int symbol = 0; symbol < num_symbols; ++symbol) {
    int count = freq[symbol];
    if (count == 0)
      continue;
    float invp = 1.0f / count;
    for (int j = 0; j < count; ++j) {
      sorted[at].second = symbol;
      sorted[at].first = invp + j * invp;
      ++at;
    }
  }
  CHECK(at == state_len);
  std::stable_sort(&sorted[0], &sorted[state_len]);
  for (int i = 0; i < state_len; ++i)
    sorted_symbols[i] = sorted[i].second;
}

class FSEEncoder {
public:
  FSEEncoder(uint8_t* buffer, int max_symbols = 256, int state_bits = 12)
    : writer_(buffer),
      max_symbols_(max_symbols),
      state_bits_(state_bits),
      state_len_(1 << state_bits_) {
    CHECK(state_bits <= 12); // Otherwise need larger table length
    memset(freq_, 0, sizeof(freq_));
    state_ = state_len_;
  }

  void scan(int symbol) {
    ++freq_[symbol];
  }

  void buildTable() {
    normalize();
    sortSymbols(state_len_, max_symbols_, freq_, sorted_symbols_);

    // http://cbloomrants.blogspot.com/2014/02/02-18-14-understanding-ans-12.html
    int next_state[256];
    int cum_prob[256];
    for (int i = 0; i < max_symbols_; ++i)
      next_state[i] = freq_[i];
    cum_prob[0] = 0;
    for (int i = 1; i < max_symbols_; ++i)
      cum_prob[i] = cum_prob[i - 1] + freq_[i - 1];
    for (int i = 0; i < state_len_; ++i) {
      int symbol = sorted_symbols_[i];
      int from_state = next_state[symbol];
      ++next_state[symbol];
      int to_state = state_len_ + i;
      packed_table_[cum_prob[symbol] + from_state - freq_[symbol]] = to_state;
    }

    // Now, build the final encoding table.
    int total = 0;
    for (int symbol = 0; symbol < max_symbols_; ++symbol) {
      if (freq_[symbol] == 0)
        continue;
      uint32_t max_bits_out = state_bits_ - log2(freq_[symbol] - 1);
      uint32_t min_state_plus = freq_[symbol] << max_bits_out;
      encoded_[symbol].delta_bits = (max_bits_out << 16) - min_state_plus;
      encoded_[symbol].delta_state = total - freq_[symbol];
      total += freq_[symbol];
    }
  }

  int64_t writeTable(uint8_t* buffer) {
    BitWriter writer(buffer);
    writer.writeBits(state_bits_, 4);

    int remaining = state_len_;
    for (int i = 0; i < max_symbols_ && remaining != 0; ++i) {
      writer.writeBits(freq_[i], log2(remaining) + 1);
      remaining -= freq_[i];
    }

    CHECK(writer_.position() >= 0 && writer_.position() < 8);
    writer.writeBits(writer_.position(), 3);

    // Byte align after the table
    return writer.finish();
  }

  void encode(int symbol) {
    // http://fastcompression.blogspot.com/2014/02/fse-tricks-memory-efficient-subrange.html
    int num_bits = (state_ + encoded_[symbol].delta_bits) >> 16;
    writer_.writeBits(state_, num_bits);

    int subrange_id = state_ >> num_bits;
    state_ = packed_table_[subrange_id + encoded_[symbol].delta_state];
  }

  int64_t finish() {
    writer_.writeBits(state_ & ((1 << state_bits_) - 1), state_bits_);
    return writer_.finish();
  }

private:
  void normalize() {
    // http://cbloomrants.blogspot.com/2014/02/02-11-14-understanding-ans-10.html
    int total = 0;
    for (int i = 0; i < max_symbols_; ++i)
      total += freq_[i];

    // normalization
    int new_total = 0;
    int max_freq = 0;
    int max_freq_i = 0;
    for (int symbol = 0; symbol < max_symbols_; ++symbol) {
      uint64_t c = freq_[symbol];
      if (c == 0)
        continue;
      if (c > max_freq) {
        max_freq = c;
        max_freq_i = symbol;
      }
      freq_[symbol] = std::max(1, int(((c << state_bits_) + (total / 2)) / total));
      LOGV(2, "scaled_freq[%d] = %d\n", symbol, freq_[symbol]);
      new_total += freq_[symbol];
    }

    // Distribute any remaining error to the largest symbol (not optimal - but it works).
    int err = new_total - state_len_;
    LOGV(2, "normalization error: %d\n", err);
    CHECK(err < freq_[max_freq_i]);
    freq_[max_freq_i] -= err;
  }

  ReverseBitWriter writer_;

  const int max_symbols_;
  int freq_[256];

  struct EncodedSymbol {
    int delta_bits;
    int delta_state;
  };
  EncodedSymbol encoded_[256];

  // state_bits_ up to 13 is low enough to fit decode_table in L1
  const int state_bits_;
  const int state_len_;
  int state_; // (2^state_bits, 2^(state_bits+1)]
  int sorted_symbols_[4096];
  int packed_table_[4096];
};

class FSEDecoder {
public:
  FSEDecoder(uint8_t* buffer, uint8_t* end)
    : br_(buffer, end) {
  }

  BitReader& br() { return br_; }

  void readTable() {
    br_.refill();
    state_bits_ = br_.readBits(4);
    state_len_ = 1 << state_bits_;

    int freq[256];
    int remaining = state_len_;
    for (num_symbols_ = 0; remaining > 0; ++num_symbols_) {
      CHECK(num_symbols_ < 256);
      br_.refill();
      freq[num_symbols_] = br_.readBits(log2(remaining) + 1);
      remaining -= freq[num_symbols_];
      if (freq[num_symbols_] > 0) {
        LOGV(2, "sym:%d len:%d remaining:%d\n", num_symbols_, freq[num_symbols_], remaining);
      }
    }
    CHECK(remaining == 0);

    int sorted_symbols[4096];
    sortSymbols(state_len_, num_symbols_, freq, sorted_symbols);

    int next_state[256];
    for (int i = 0; i < num_symbols_; ++i)
      next_state[i] = freq[i];
    for (int i = 0; i < state_len_; ++i) {
      int symbol = sorted_symbols[i];
      decode_[i].symbol = symbol;
      int from_state = next_state[symbol];
      ++next_state[symbol];
      decode_[i].num_bits = state_bits_ - log2(from_state);
      decode_[i].state = (from_state << decode_[i].num_bits) - state_len_;
    }

    int position = br_.readBits(3);

    // Ensure we catch up to be byte aligned.
    br_.byteAlign();

    // Start reading reversed bitstream.
    br_ = BitReader(br_.cursor(), br_.end(), 8-position);
    state_ = br_.readBits(state_bits_);
  }

  void decode(uint8_t* output, uint8_t* output_end) {
    uint8_t* src = br_.current();
    uint8_t* src_end = br_.end();
    int position = br_.position();
    uint32_t bits = br_.bits();

    for (;;) {
      *output++ = decode_[state_].symbol;
      if (output >= output_end) {
        break;
      }
      int len = decode_[state_].num_bits;
      while (position >= 0) {
        bits |= (src < src_end ? *src : 0) << position;
        position -= 8;
        ++src;
      }
      int n = bits >> (32 - len);
      state_ = decode_[state_].state + n;
      bits <<= len;
      position += len;
    }
  }

  uint8_t decodeOne() {
    int symbol = decode_[state_].symbol;
    int len = decode_[state_].num_bits;
    br_.refill();
    int n = br_.readBits(len);
    state_ = decode_[state_].state + n;
    return symbol;
  }

private:
  struct DecodeEntry {
    int state;
    int num_bits;
    int symbol;
  };

  BitReader br_;
  int state_;
  int state_bits_;
  int state_len_;
  int num_symbols_;
  DecodeEntry decode_[4096];
};

// From https://github.com/skeeto/hash-prospector
uint32_t hash32(uint32_t x) {
  x ^= x >> 18;
  x *= uint32_t(0xa136aaad);
  x ^= x >> 16;
  x *= uint32_t(0x9f6d62d7);
  x ^= x >> 17;
  return x;
}

int matchLength(uint8_t* src, uint8_t* match, uint8_t* end) {
  // Do a fast match against the first 4 bytes.  Note that this
  // excludes matches with length less than 4, but matches that
  // small are not a good use of bits.
  uint32_t* s32 = reinterpret_cast<uint32_t*>(src);
  uint32_t* m32 = reinterpret_cast<uint32_t*>(match);
  if (*s32 != *m32) {
    return 0;
  }

  int len = 4;
  while (src + len < end && src[len] == match[len]) {
    ++len;
  }
  return len;
}

class MatchFinder {
public:
  MatchFinder(int64_t window_size)
    : window_size_(window_size),
      window_mask_(window_size - 1) {
    ht_.resize(window_size, -window_size);
    chain_.resize(window_size, -window_size);
  }

  // Insert `pos` into the hash chain without checking for matches.
  void insert(uint8_t* buf, int64_t pos) {
    int key = hash32(buf[pos] | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) & window_mask_;
    chain_[pos & window_mask_] = ht_[key];
    ht_[key] = pos;
  }

  // Insert `pos` into the hash chain, and check for best match.
  // Returns length of best match found.  match_pos contains offset of best match.
  int findMatch(uint8_t* buf, uint8_t* buf_end, int64_t pos, int64_t& match_pos) {
    int best_match_len = 0;

    int key = hash32(buf[pos] | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) & window_mask_;
    int64_t next = ht_[key];

    int64_t min_pos = pos - window_size_;
    int hits = 0;
    // Limit the number of hash buckets we search, otherwise the search can blow up
    // for larger window sizes.
    while (next > min_pos && ++hits < FLAG_max_matches) {
      int match_len = matchLength(&buf[pos], &buf[next], buf_end);
      if (match_len > best_match_len) {
        best_match_len = match_len;
        match_pos = next;
      }

      next = chain_[next & window_mask_];
    }

    // Insert new match
    chain_[pos & window_mask_] = ht_[key];
    ht_[key] = pos;

    return best_match_len;
  }

  // Insert `pos` into the hash chain, and check for best match.
  // Returns length of best match found.  match_pos contains offset of best match.
  int findMatches(uint8_t* buf, uint8_t* buf_end, int64_t pos, int64_t* match_dist, int64_t* match_len) {
    int key = hash32(buf[pos] | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) & window_mask_;
    int64_t next = ht_[key];
    int64_t min_pos = pos - window_size_;

    int matches = 0;
    int hits = 0;
    // Limit the number of hash buckets we search, otherwise the search can blow up
    // for larger window sizes.
    while (next > min_pos && ++hits < FLAG_max_matches) {
      int len = matchLength(&buf[pos], &buf[next], buf_end);
      if (len > 0) {
        match_dist[matches] = pos - next;
        match_len[matches] = len;
        ++matches;
      }

      next = chain_[next & window_mask_];
    }

    // Insert new match
    chain_[pos & window_mask_] = ht_[key];
    ht_[key] = pos;

    return matches;
  }

private:
  int64_t window_size_;
  int64_t window_mask_;
  std::vector<int> ht_;
  std::vector<int> chain_;
};

int lengthCode(int length) {
  if (length <= 15) {
    return length;
  }
  return 12 + log2(length);
}

int lengthExtra(int length) {
  return length - (1 << log2(length));
}

int offsetCode(int offset) {
  if (offset < 2) {
    return offset;
  }
  return 1 + log2(offset);
}

int offsetExtra(int offset) {
  return offset - (1 << log2(offset));
}

template<int bytes>
int readInt(uint8_t* buf) {
  int v = 0;
  for (int i = 0; i < bytes; ++i) {
    v |= buf[i] << (i * 8);
  }
  return v;
}

template<int bytes>
void writeInt(uint8_t* buf, int v) {
  for (int i = 0; i < bytes; ++i) {
    *buf++ = v & 0xff;
    v >>= 8;
  }
}

int literal_price(int c) {
  return 6;
}

int match_price(int len, int dist) {
  int len_cost = 6 + log2(len);
  int dist_cost = std::max(0, log2(dist) - 3);
  return len_cost + dist_cost;
}

class LzEncoder {
public:
  // Initializes encoder with a backwards window of `window_size`.  Must be a power of 2!
  LzEncoder(int64_t window_size, int level)
   : matcher_(window_size),
     level_(level) {
  }

  // Compresses `buffer` from `buffer+p` to `buffer+p_end`.
  // Writes compressed sequence to `out`.  `out` must contain at least `window_size` bytes!
  // Returns number of bytes written to `out`.
  int64_t encode(uint8_t* buffer, int64_t p, int64_t p_end, uint8_t* out) {
    uint8_t* out_start = out;

    num_seq_ = 0;
    num_lit_ = 0;

    if (level_ == 0) {
      fastParse(buffer, p, p_end);
    } else if (level_ == 1) {
      optimalParse(buffer, p, p_end);
    }

    // Write literal section
    {
      // Uncompressed length
      writeInt<3>(out, num_lit_);
      out += 3;
      // Compressed length
      uint8_t* marker = out;
      out += 3;

      // Huffman table for literals
      HuffmanEncoder encoder(out);
      for (int i = 0; i < num_lit_; ++i) {
        encoder.scan(literals_[i]);
      }
      encoder.buildTable();
      for (int i = 0; i < num_lit_; ++i) {
        encoder.encode(literals_[i]);
      }
      int64_t bytes_written = encoder.finish();
      out += bytes_written;
      writeInt<3>(marker, bytes_written);
      LOGV(1, "literals: %d -> %lld\n", num_lit_, bytes_written);
    }

    // Write sequences section
    writeInt<3>(out, num_seq_);
    out += 3;

    // a. Literal lengths
    int lit_len_out = writeValues<false>(out, literal_lengths_);
    out += lit_len_out;
    // b. Match offsets
    int match_offsets_out = writeValues<true>(out, match_offsets_);
    out += match_offsets_out;
    // c. Match lengths
    int match_lengths_out = writeValues<false>(out, match_lengths_);
    out += match_lengths_out;

    LOGV(1, "Wrote block, %d sequences, %d literals, lit_len:%d match_offsets:%d match_lengths:%d\n",
         num_seq_, num_lit_, lit_len_out, match_offsets_out, match_lengths_out);

    return out - out_start;
  }

private:
  void fastParse(uint8_t* buffer, int64_t p, int64_t p_end) {
    const int kMinMatchLen = 5;
    int num_literals = 0;

    for (int64_t i = p; i < p_end; ++i) {
      // Output a match?  Or a literal?
      int64_t match_pos;
      int match_len = matcher_.findMatch(buffer, buffer + p_end, i, match_pos);
      if (match_len >= kMinMatchLen && i < p_end - 4) {
        match_offsets_[num_seq_] = i - match_pos;
        match_lengths_[num_seq_] = match_len;
        literal_lengths_[num_seq_] = num_literals;
        ++num_seq_;
        num_literals = 0;

        while (--match_len > 0) {
          matcher_.insert(buffer, ++i);
        }
      } else {
        literals_[num_lit_++] = buffer[i];
        ++num_literals;
      }
    }
    if (num_literals != 0) {
      literal_lengths_[num_seq_] = num_literals;
      match_offsets_[num_seq_] = 0;
      match_lengths_[num_seq_] = 0;
      ++num_seq_;
    }
  }

  void optimalParse(uint8_t* buffer, int64_t p, int64_t p_end) {
    int64_t length = p_end - p;
    std::vector<int> price(length + 1, 999999999);
    std::vector<int> len(length + 1, 0);
    std::vector<int> dist(length + 1, 0);

    price[0] = 0;

    // Forward pass, calculate best price for literal or match at each position.
    for (int64_t i = 0; i < length; ++i) {
      int lit_cost = price[i] + literal_price(buffer[i]);
      if (lit_cost < price[i + 1]) {
        price[i + 1] = lit_cost;
        len[i + 1] = 1;
        dist[i + 1] = 0;
      }

      // Don't try matches close to end of buffer.
      if (i + 4 >= length) {
        continue;
      }

      int64_t match_dist[16], match_len[16];
      int matches = matcher_.findMatches(buffer, buffer + p_end, p + i, match_dist, match_len);
      for (int j = 0; j < matches; ++j) {
        int match_cost = price[i] + match_price(match_len[j], match_dist[j]);
        if (match_cost < price[i+ match_len[j]]) {
          price[i + match_len[j]] = match_cost;
          len[i + match_len[j]] = match_len[j];
          dist[i + match_len[j]] = match_dist[j];
        }
      }
    }

    // Backward pass, pick best option at each step.
    if (len[length] <= 1) {
      match_offsets_[num_seq_] = 0;
      match_lengths_[num_seq_] = 0;
      literal_lengths_[num_seq_] = 0;
      ++num_seq_;
    }
    for (int64_t i = length; i > 0;) {
      if (len[i] > 1) {
        match_offsets_[num_seq_] = dist[i];
        match_lengths_[num_seq_] = len[i];
        literal_lengths_[num_seq_] = 0;
        ++num_seq_;
        i -= len[i];
      } else {
        literals_[num_lit_++] = buffer[p + i - 1];
        ++literal_lengths_[num_seq_ - 1];
        --i;
      }
    }

    // We wrote the arrays in reverse, flip them for uniformity.
    std::reverse(&literal_lengths_[0], &literal_lengths_[num_seq_]);
    std::reverse(&match_offsets_[0], &match_offsets_[num_seq_]);
    std::reverse(&match_lengths_[0], &match_lengths_[num_seq_]);
    std::reverse(&literals_[0], &literals_[num_lit_]);
  }

  template<bool is_offset>
  int64_t writeValues(uint8_t* out, const int* values) {
    HuffmanEncoder encoder(out, 32);
    for (int i = 0; i < num_seq_; ++i) {
      encoder.scan(is_offset ? offsetCode(values[i]) : lengthCode(values[i]));
    }
    encoder.buildTable();
    for (int i = 0; i < num_seq_; ++i) {
      int v = values[i];
      encoder.encode(is_offset ? offsetCode(v) : lengthCode(v));
      LOGV(3, "Encoding %d -> %d (%d, %d)\n",
           v, is_offset ? offsetCode(v) : lengthCode(v), log2(v),
           is_offset ? offsetExtra(v) : lengthExtra(v));
      if (v >= (is_offset ? 2 : 16)) {
        int extra = is_offset ? offsetExtra(v) : lengthExtra(v);
        encoder.writer().writeBits(extra, log2(v));
      }
    }
    return encoder.finish();
  }

  MatchFinder matcher_;
  int level_;

  int num_seq_;
  int num_lit_;
  uint8_t literals_[kMaxChunkSize];
  int match_offsets_[kMaxChunkSize / 4];
  int match_lengths_[kMaxChunkSize / 4];
  int literal_lengths_[kMaxChunkSize / 4];
};

class LzDecoder {
public:
  bool decode(uint8_t* buf, uint8_t* end, uint8_t* out, uint8_t* out_end) {
    uint8_t literals[kMaxChunkSize];
    int literal_lengths[kMaxChunkSize / 4];
    int match_offsets[kMaxChunkSize / 4];
    int match_lengths[kMaxChunkSize / 4];

    {
      int num_literals = readInt<3>(buf);
      int compressed_size = readInt<3>(buf + 3);
      buf += 6;
      LOGV(1, "Read %d literals, %d compressed bytes\n", num_literals, compressed_size);

      HuffmanDecoder decoder(buf, buf + compressed_size);
      decoder.readTable();
      decoder.decode(literals, literals + num_literals);
      buf += compressed_size;
    }

    int num_seq = readInt<3>(buf);
    buf += 3;
    LOGV(1, "Read %d sequences\n", num_seq);

    buf += decodeValues<false>(buf, end, num_seq, literal_lengths);
    buf += decodeValues<true>(buf, end, num_seq, match_offsets);
    buf += decodeValues<false>(buf, end, num_seq, match_lengths);

    uint8_t* out_dbg = out;

    uint8_t* l_head = literals;
    for (int i = 0; i < num_seq; ++i) {
      LOGV(3, "Sequence (lit_len:%d, match_offset:%d, match_length:%d)\n",
           literal_lengths[i], match_offsets[i], match_lengths[i]);
      for (int j = 0; j < literal_lengths[i]; ++j) {
        *out++ = *l_head++;
      }
      uint8_t* match_base = out - match_offsets[i];
      for (int j = 0; j < match_lengths[i]; ++j) {
        *out++ = match_base[j];
      }
    }
    return true;
  }

private:
  template<bool is_offset>
  int64_t decodeValues(uint8_t* buf, uint8_t* end, int num_seq, int* values) {
    const int kSymBits = 5;
    HuffmanDecoder decoder(buf, end, kSymBits);
    decoder.readTable();
    for (int i = 0; i < num_seq; ++i) {
      int v = decoder.decodeOne();
      if (v >= (is_offset ? 2 : 16)) {
        int extra_bits = v - (is_offset ? 1 : 12);
        v = 1 << extra_bits;
        decoder.br().refill();
        v |= decoder.br().readBits(extra_bits);
      }
      values[i] = v;
    }
    decoder.br().byteAlign();
    return decoder.br().cursor() - buf;
  }
};

int64_t lzCompress(uint8_t* buf, int64_t len, uint8_t* out) {
  uint8_t* out_start = out;
  int64_t chunk_size = 1 << 18; // 256k
  LzEncoder lz_encoder(1 << FLAG_window_size, FLAG_level);

  for (int64_t start = 0; start < len; start += chunk_size) {
    int64_t remaining = std::min(chunk_size, len - start);
    uint8_t* marker = out;
    out += 3;

    int64_t chunk_written = lz_encoder.encode(buf, start, start + remaining, out);
    writeInt<3>(marker, chunk_written);

    out += chunk_written;
  }
  return out - out_start;
}

void lzDecompress(uint8_t* buf, int64_t len, uint8_t* out, int64_t out_len) {
  int64_t read = 0;
  int64_t chunk_size = 1 << 18; // 256k
  uint8_t* buf_end = buf + len;
  LzDecoder decoder;
  while (buf < buf_end) {
    int compressed_size = readInt<3>(buf);
    buf += 3;

    CHECK(decoder.decode(buf, buf + compressed_size, out, out + std::min(chunk_size, out_len)));

    buf += compressed_size;
    out += chunk_size;
    out_len -= chunk_size;
  }
}

std::unique_ptr<uint8_t> readEnwik8(int64_t& len) {
  FILE* f = fopen("enwik8", "r");
  // FILE* f = fopen("data/silesia.tar", "r");
  fseek(f, 0, SEEK_END);
  len = ftell(f);
  fseek(f, 0, SEEK_SET);

  std::unique_ptr<uint8_t> buf;
  buf.reset(new uint8_t[len]);
  fread(buf.get(), 1, len, f);
  return std::move(buf);
}

int testBitReader(uint8_t* buf, uint8_t* out, int64_t len) {
  BitReader orig_reader(buf, buf + len);
  BitWriter writer(out);
  for (int64_t i = 0; i < 8 * len; ++i) {
    orig_reader.refill();
    writer.writeBit(orig_reader.readBit());
  }

  BitReader reader(out, out + len);
  for (int64_t i = 0; i < len; ++i) {
    reader.refill();
    uint8_t orig = buf[i];
    uint8_t written = reader.readBits(8);
    if (orig != written) {
      fprintf(stderr, "busted %lld,%d,%d\n", i, orig, written);
      return 1;
    }
  }

  return 0;
}

int checkBytes(uint8_t* buf, uint8_t* actual, int64_t len) {
  int bad = 0;
  for (int64_t i = 0; i < len; ++i) {
    uint8_t orig = actual[i];
    uint8_t v = buf[i];
    if (orig != v) {
      if (++bad > 20) {
        fprintf(stderr, "more than 20 busted\n");
        break;
      }
      fprintf(stderr, "bad idx:%lld,orig:%d,decoded:%d\n", i, orig, v);
    }
  }
  return bad;
}

bool testHuffman(uint8_t* buf, uint8_t* out, int64_t len) {
  Timer timer;
  HuffmanEncoder encoder(out);
  for (int64_t i = 0; i < len; ++i) {
    encoder.scan(buf[i]);
  }
  encoder.buildTable();
  for (int64_t i = 0; i < len; ++i) {
    encoder.encode(buf[i]);
  }
  int64_t encoded_size = encoder.finish();

  std::unique_ptr<uint8_t> decoded;
  decoded.reset(new uint8_t[len]);
  HuffmanDecoder decoder(out, out + encoded_size);
  decoder.readTable();
  decoder.decode(decoded.get(), decoded.get() + len);

  return checkBytes(decoded.get(), buf, len) == 0;
}

void huffmanSpeed() {
  int64_t len;
  std::unique_ptr<uint8_t> buf = readEnwik8(len);
  // len = 10000;
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  int64_t encoded_size;
  {
    Timer timer;
    const int kIters = 1;
    for (int i = 0; i < kIters; ++i) {
      encoded_size = huffmanCompress(buf.get(), len, out.get());
    }
    double elapsed = timer.elapsed() / 1000;
    printf("Encoded %lld into %lld bytes\n", len, encoded_size);
    printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len * kIters / (1024. * 1024.)) / elapsed);
  }

  {
    Timer timer;
    huffmanDecompress(out.get(), encoded_size, buf.get(), len);
    double elapsed = timer.elapsed() / 1000;
    printf("Decompression\n");
    printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);
  }
  {
    std::unique_ptr<uint8_t> truth = readEnwik8(len);
    for (int i = 0; i < len; ++i) {
      CHECK(truth.get()[i] == buf.get()[i]);
    }
    printf("Decompression validated!\n");
  }
}

void tuneSettings() {
  uint8_t* buf;
  int64_t len;

  std::unique_ptr<uint8_t> enwik8 = readEnwik8(len);
  buf = enwik8.get();
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  for (int level = 0; level <= 1; ++level) {
    for (int window_size = /*14*/26; window_size <= 26; window_size += 4) {
      for (int matches = /*2*/16; matches <= 16; matches += 2) {
        FLAG_level = level;
        FLAG_window_size = window_size;
        FLAG_max_matches = matches;

        Timer timer;
        int64_t encoded_size = lzCompress(buf, len, out.get());
        double elapsed = timer.elapsed() / 1000;
        printf("level:%d, window:%d, matches:%d, %lld bytes, %.2lf seconds, %.2lf MB/s\n", level, window_size, matches, encoded_size, elapsed, (len / (1024. * 1024.)) / elapsed);
      }
    }
  }
}

void testLz() {
  uint8_t* buf;
  int64_t len;

  std::unique_ptr<uint8_t> enwik8 = readEnwik8(len);
  buf = enwik8.get();
  // len = 10000000;
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);


  Timer timer;
  int64_t encoded_size = lzCompress(buf, len, out.get());
  printf("Encoded %lld into %lld bytes\n", len, encoded_size);
  double elapsed = timer.elapsed() / 1000;
  printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);

  std::unique_ptr<uint8_t> decoded;
  decoded.reset(new uint8_t[len]);
  timer = Timer();
  lzDecompress(out.get(), encoded_size, decoded.get(), len);
  elapsed = timer.elapsed() / 1000;
  printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);

  checkBytes(decoded.get(), buf, len);
}

void testShort() {
  std::vector<std::string> tests{
    "ABABABABCAAAABBBBABC",
    "ABCDEFGHIJKLMNOPQRS",
    "AAAAAAAABBBBBBBCCCCD",
  };
  tests.push_back(tests[0] + tests[0] + tests[0] + tests[0] + tests[0]);
  for (auto& test : tests) {
    int64_t len = test.size();
    uint8_t* buf = reinterpret_cast<uint8_t*>(&test[0]);
    std::unique_ptr<uint8_t> out;
    out.reset(new uint8_t[100+len]);
    int64_t encoded_size = huffmanCompress(buf, len, out.get());
    std::unique_ptr<uint8_t> decoded;
    decoded.reset(new uint8_t[len]);
    huffmanDecompress(out.get(), encoded_size, decoded.get(), len);
    checkBytes(decoded.get(), buf, len);
  }
}

void testFSEEncoder() {
  std::vector<std::string> tests{
    "ABABABABCAAAABBBBABC",
    "ABCDEFGHIJKLMNOPQRS",
    "AAAAAAAABBBBBBBCCCCD",
  };
  tests.push_back(tests[0] + tests[0] + tests[0] + tests[0] + tests[0]);
  for (auto& test : tests) {
    int64_t len = test.size();
    uint8_t* buf = reinterpret_cast<uint8_t*>(&test[0]);
    std::unique_ptr<uint8_t> out;
    int out_size = 512 + len;
    out.reset(new uint8_t[out_size]);
    FSEEncoder encoder(out.get() + out_size);
    for (int64_t i = 0; i < len; ++i) {
      encoder.scan(buf[i]);
    }
    encoder.buildTable();
    for (int64_t i = len - 1; i >= 0; --i) {
      encoder.encode(buf[i]);
    }
    int64_t encoded_size = encoder.finish();
    int64_t table_size = encoder.writeTable(out.get());
    uint8_t* out_start = out.get() + out_size - encoded_size;
    memmove(out_start - table_size, out.get(), table_size);
    printf("Original: %lld Encoded size: %lld\n", len, encoded_size);

    std::unique_ptr<uint8_t> decoded;
    decoded.reset(new uint8_t[len]);
    {
      FSEDecoder decoder(out_start - table_size, out_start + encoded_size);
      decoder.readTable();
      decoder.decode(decoded.get(), decoded.get() + len);
      CHECK(checkBytes(decoded.get(), buf, len) == 0);
    }
    {
      FSEDecoder decoder(out_start - table_size, out_start + encoded_size);
      decoder.readTable();
      for (int64_t i = 0; i < len; ++i) {
        decoded.get()[i] = decoder.decodeOne();
      }
      CHECK(checkBytes(decoded.get(), buf, len) == 0);
    }
  }
}

void tests() {
  int64_t len;
  std::unique_ptr<uint8_t> buf = readEnwik8(len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  testBitReader(buf.get(), out.get(), 1000);
  for (int i = 1; i < 1000; i += 50) {
    CHECK(testHuffman(buf.get(), out.get(), i));
  }
}

int main(int argc, char const* argv[]) {
  if (FLAG_test) {
    tests();
    return 0;
  }

  //huffmanSpeed();
  //testShort();
  testFSEEncoder();

  //testLz();
  //tuneSettings();

  return 0;
}
