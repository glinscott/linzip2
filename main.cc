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

constexpr int kDebugLevel = 0;

#define CHECK(cond) do{if(!(cond)){fprintf(stderr,"%s:%d CHECK %s\n", __FILE__, __LINE__, #cond);exit(1);}}while(0);
#define LOGV(level, s, ...) do{if(level<=kDebugLevel) fprintf(stderr, s, ##__VA_ARGS__);}while(0);

struct Timer {
  Timer() : time_(std::chrono::high_resolution_clock::now()) {}
  double elapsed() const { return std::chrono::duration<double, std::milli>(std::chrono::high_resolution_clock::now()-time_).count(); }
  std::chrono::high_resolution_clock::time_point time_;
};

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
  } else {
    return 0;
  }
}

class BitReader {
public:
  BitReader(uint8_t* buffer, uint8_t* end)
    : current_(buffer),
      end_(end) {
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

  uint8_t* end() const {
    return end_;
  }

  uint32_t bits() const {
    return bits_;
  }

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
    writer_.writeBits(num_symbols, kSymBits);

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
    num_symbols_ = br_.readBits(sym_bits_);

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
    const int kNumHits = 16;
    while (next > min_pos && ++hits < kNumHits) {
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
    const int kNumHits = 16;
    while (next > min_pos && ++hits < kNumHits) {
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

int literalLengthCode(int literal_length) {
  if (literal_length <= 15) {
    return literal_length;
  }
  return 12 + log2(literal_length);
}

int literalLengthExtra(int literal_length) {
  if (literal_length <= 15) {
    return 0;
  }
  return literal_length - (1 << log2(literal_length));
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
  int len_cost = 3;
  len_cost += std::max(0, log2(len_cost) - 3);

  int dist_cost = 3;
  dist_cost += std::max(0, log2(dist_cost) - 3);

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

    /*
    for (int i = 0; i < literal_lengths.size(); ++i) {
      printf("lit:%d, %d, %d\n", literal_lengths[i], match_offsets[i], match_lengths[i]);
    }
    for (int i = 0; i < literals.size(); ++i) {
      printf("%c,", literals[i]);
    }
    printf("\n----\n");
    */

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

    /*
    for (int i = 0; i < literal_lengths.size(); ++i) {
      LOGV(2, "Encoding (lit_len:%d, match_offset:%d, match_length:%d)\n", literal_lengths[i], match_offsets[i], match_lengths[i]);
    }
    */

    // a. Literal lengths
    int lit_len_out = writeValues(out, literal_lengths_, num_seq_);
    out += lit_len_out;
    // b. Match offsets
    int match_offsets_out = writeValues(out, match_offsets_, num_seq_);
    out += match_offsets_out;
    // c. Match lengths
    int match_lengths_out = writeValues(out, match_lengths_, num_seq_);
    out += match_lengths_out;

    LOGV(1, "Wrote block, %d sequences, %d literals, lit_len:%d match_offsets:%d match_lengths:%d\n",
         num_seq_, num_lit_, lit_len_out, match_offsets_out, match_lengths_out);

    return out - out_start;
  }

private:
  void fastParse(uint8_t* buffer, int64_t p, int64_t p_end) {
    int num_literals = 0;

    for (int64_t i = p; i < p_end; ++i) {
      // Output a match?  Or a literal?
      int64_t match_pos;
      int match_len = matcher_.findMatch(buffer, buffer + p_end, i, match_pos);
      if (match_len != 0 && i < p_end - 4) {
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
        int match_cost = price[i] + match_price(match_len[j], -match_dist[j]);
        if (match_cost < price[i+ match_len[j]]) {
          price[i + match_len[j]] = match_cost;
          len[i + match_len[j]] = match_len[j];
          dist[i + match_len[j]] = match_dist[j];
        }
      }

      //printf("(%d, %d, %d)\n", price[i], len[i], dist[i]);
    }
    //printf("----\n");

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

    std::reverse(&literal_lengths_[0], &literal_lengths_[num_seq_]);
    std::reverse(&match_offsets_[0], &match_offsets_[num_seq_]);
    std::reverse(&match_lengths_[0], &match_lengths_[num_seq_]);
    std::reverse(&literals_[0], &literals_[num_lit_]);
  }

  int64_t writeValues(uint8_t* out, const int* values, int num_seq) {
    HuffmanEncoder encoder(out, 32);
    for (int i = 0; i < num_seq; ++i) {
      encoder.scan(literalLengthCode(values[i]));
    }
    encoder.buildTable();
    for (int i = 0; i < num_seq; ++i) {
      int v = values[i];
      encoder.encode(literalLengthCode(v));
      LOGV(3, "Encoding %d -> %d (%d, %d)\n", v, literalLengthCode(v), log2(v), literalLengthExtra(v));
      if (v >= 16) {
        int extra = literalLengthExtra(v);
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

    buf += decodeValues(buf, end, num_seq, literal_lengths);
    buf += decodeValues(buf, end, num_seq, match_offsets);
    buf += decodeValues(buf, end, num_seq, match_lengths);

    uint8_t* l_head = literals;
    for (int i = 0; i < num_seq; ++i) {
      LOGV(2, "Sequence (lit_len:%d, match_offset:%d, match_length:%d)\n", literal_lengths[i], match_offsets[i], match_lengths[i]);
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
  int64_t decodeValues(uint8_t* buf, uint8_t* end, int num_seq, int* values) {
    const int kSymBits = 5;
    HuffmanDecoder decoder(buf, end, kSymBits);
    decoder.readTable();
    for (int i = 0; i < num_seq; ++i) {
      int v = decoder.decodeOne();
      if (v >= 16) {
        int extra_bits = v - 12;
        v = 1 << extra_bits;
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
  LzEncoder lz_encoder(chunk_size, 1);

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
  // printf("Encoded %lld into %lld bytes\n", len, encoded_size);
  // double elapsed = timer.elapsed() / 1000;
  // printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);

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

void testLz() {
  int64_t len;
  std::unique_ptr<uint8_t> enwik8 = readEnwik8(len);
  len = 10000000;
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  //std::string test = "ABABABABCAAAABBBBABC";
  //test = test + test + test + test + test;
  //std::string test = "ABCDEFGHIJKLMNOPQRS";
  //len = test.size();
  //uint8_t* buf = reinterpret_cast<uint8_t*>(&test[0]);

  uint8_t* buf = enwik8.get();
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
  std::string test = "AAAAAAAABBBBBBBCCCCD";
  int64_t len = test.size();
  uint8_t* buf = reinterpret_cast<uint8_t*>(&test[0]);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[100+len]);
  int64_t encoded_size = huffmanCompress(buf, len, out.get());
  printf("Encoded into %lld\n", encoded_size);
}

int main() {
  /*
  int64_t len;
  std::unique_ptr<uint8_t> buf = readEnwik8(len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  testBitReader(buf.get(), out.get(), 1000);
  for (int i = 1; i < 1000; i += 50) {
    CHECK(testHuffman(buf.get(), out.get(), i));
  }
  */

  //huffmanSpeed();
  // testShort();

  testLz();

  return 0;
}
