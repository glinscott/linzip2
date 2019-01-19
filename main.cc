#include <algorithm>
#include <chrono>
#include <cstdio>
#include <cmath>
#include <cstdlib>
#include <cstdint>
#include <queue>
#include <string>
#include <vector>

constexpr int kDebugLevel = 0;

#define CHECK(cond) do{if(!(cond)){fprintf(stderr,"%s:%d CHECK %s\n", __FILE__, __LINE__, #cond);exit(1);}}while(0);
#define LOGV(level, s, ...) do{if(level<=kDebugLevel) fprintf(stderr, s, ##__VA_ARGS__);}while(0);

struct Timer {
  Timer() : time_(std::chrono::high_resolution_clock::now()) {}
  double elapsed() const { return std::chrono::duration<double, std::milli>(std::chrono::high_resolution_clock::now()-time_).count(); }
  std::chrono::high_resolution_clock::time_point time_;
};

std::string toBinary(int v, int size) {
  std::string result;
  for (int j = 0; j < size; ++j) {
    result += ((v>>(size-j-1))&1) ? "1" : "0";
  }
  return result;
}

struct ChunkHeader {
  uint8_t flags;
};

int log2(int v) {
  if (v > 0) {
    return 32 - __builtin_clz(v) - 1;
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
  HuffmanEncoder(uint8_t* buffer)
    : writer_(buffer) {
    for (int i = 0; i < 256; ++i) {
      freq_[i].symbol = i;
    }
  }

  BitWriter& writer() { return writer_; }

  void scan(int symbol) {
    ++freq_[symbol].freq;
  }

  void writeTable(int num_symbols) {
    writer_.writeBits(num_symbols, 8);

    int code = 0;
    int last_level = -1;
    for (int i = 0; i < num_symbols; ++i) {
      int level = freq_[i].freq;
      if (last_level != level) {
        if (last_level != -1) {
          ++code;
          code <<= (level - last_level);
        }
        last_level = level;
      } else {
        ++code;
      }

      int symbol = freq_[i].symbol;
      length_[symbol] = level;
      code_[symbol] = code;

      writer_.writeBits(freq_[i].symbol, 8);
      writer_.writeBits(level - 1, 4);

      LOGV(2, "code:%s hex:%x level:%d symbol:%d\n", toBinary(code, level).c_str(), code, level, symbol);
    }

    // Byte align after the table
    writer_.finish();
  }

  void limitLength(int num_symbols) {
    // Limit the maximum code length
    int k = 0;
    int maxk = (1 << kMaxHuffCodeLength) - 1;
    for (int i = num_symbols - 1; i >= 0; --i) {
      freq_[i].freq = std::min(freq_[i].freq, 11);
      k += 1 << (kMaxHuffCodeLength - freq_[i].freq);
    }
    LOGV(3, "k before: %.6lf\n", k / double(maxk));
    for (int i = num_symbols - 1; i >= 0 && k > maxk; --i) {
      while (freq_[i].freq < kMaxHuffCodeLength) {
        ++freq_[i].freq;
        k -= 1 << (kMaxHuffCodeLength - freq_[i].freq);
      }
    }
    LOGV(3, "k pass1: %.6lf\n", k / double(maxk));
    for (int i = 0; i < num_symbols; ++i) {
      while (k + (1 << (kMaxHuffCodeLength - freq_[i].freq)) <= maxk) {
        k += 1 << (kMaxHuffCodeLength - freq_[i].freq);
        --freq_[i].freq;
      }
    }
    LOGV(3, "k pass2: %x, %x\n", k, maxk);
  }

  void buildTable() {
    int idx = 256;

    std::priority_queue<Node*, std::vector<Node*>, Comparator> q;
    const int kSentinel = 9999;
    int num_symbols = 0;
    for (int i = 0; i < 256; ++i) {
      if (freq_[i].freq) {
        q.push(&freq_[i]);
        ++num_symbols;
      } else {
        freq_[i].freq = kSentinel;
      }
    }

    while (q.size() > 1) {
      Node* n1 = q.top();
      q.pop();
      Node* n2 = q.top();
      q.pop();

      Node* add = &freq_[idx++];
      add->symbol = -1;
      add->l = n2;
      add->r = n1;
      add->freq = n1->freq + n2->freq;
      q.push(add);
    }

    walk(q.top(), num_symbols == 1 ? 1 : 0);

    // TODO: Not efficient...
    std::sort(&freq_[0], &freq_[256], [](const Node& l, const Node& r){return l.freq < r.freq;});

    limitLength(num_symbols);
    writeTable(num_symbols);
  }

  void walk(Node* n, int level) {
    if (n->symbol != -1) {
      n->freq = level;
      return;
    }

    walk(n->l, level + 1);
    walk(n->r, level + 1);
  }

  void encode(int symbol) {
    writer_.writeBits(code_[symbol], length_[symbol]);
  }

  int64_t finish() {
    return writer_.finish();
  }

private:
  BitWriter writer_;

  Node freq_[512] = {0};

  uint8_t length_[256] = {0};
  int code_[256] = {0};
};

class HuffmanDecoder {
public:
  HuffmanDecoder(uint8_t* buffer, uint8_t* end)
    : br_(buffer, end) {
  }

  BitReader& br() { return br_; }

  bool readTable() {
    int sym_bits = 8;

    br_.refill();
    num_symbols_ = br_.readBits(sym_bits);

    CHECK(num_symbols_ <= kMaxSymbols);

    for (int i = 0; i < num_symbols_; ++i) {
      br_.refill();
      int symbol = br_.readBits(sym_bits);
      int codelen = br_.readBits(4) + 1;
      LOGV(2, "sym:%d len:%d\n", symbol, codelen);

      ++codelen_count_[codelen];
      last_used_symbol_ = symbol;
      symbol_length_[i] = codelen;
      symbol_[i] = symbol;
      min_codelen_ = std::min(min_codelen_, codelen);
      max_codelen_ = std::max(max_codelen_, codelen);
    }
    LOGV(1, "num_sym %d codelen(min:%d, max:%d)\n", num_symbols_, min_codelen_, max_codelen_);

    // Ensure we catch up to be byte aligned.
    br_.byteAlign();

    return true;
  }

  bool assignCodes() {
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

    return true;
  }

  bool decode(uint8_t* output, uint8_t* output_end) {
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
    return true;
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
  BitReader br_;
  int num_symbols_;
  int last_used_symbol_;
  int min_codelen_ = 255;
  int max_codelen_ = 0;
  int codelen_count_[17] = {0};
  uint8_t symbol_length_[kMaxSymbols] = {0}; 

  uint8_t symbol_[256] = {0};
  uint8_t bits_to_sym_[0x800] = {0};
  uint8_t bits_to_len_[0x800] = {0};
};

int64_t huffmanCompress(uint8_t* buf, int64_t len, uint8_t* out) {
  uint8_t* out_start = out;
  int64_t chunk_size = 1 << 18; // 256k
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
  int64_t chunk_size = 1 << 18; // 256k
  uint8_t* buf_end = buf + len;
  while (buf < buf_end) {
    int compressed_size = buf[0] | (buf[1] << 8) | (buf[2] << 16);
    buf += 3;

    HuffmanDecoder decoder(buf, buf + compressed_size);
    CHECK(decoder.readTable());
    CHECK(decoder.assignCodes());
    CHECK(decoder.decode(out, out + std::min(chunk_size, out_len)));

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

class MatchFinder {
public:
  MatchFinder(int64_t window_size)
    : window_size_(window_size),
      window_mask_(window_size - 1) {
    ht_.resize(window_size, -window_size);
    chain_.resize(window_size, -window_size);
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

  void insert(uint8_t* buf, int64_t pos) {
    int key = hash32(buf[pos] | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) & window_mask_;
    chain_[pos & window_mask_] = ht_[key];
    ht_[key] = pos;
  }

  int findMatch(uint8_t* buf, uint8_t* buf_end, int64_t pos, int64_t& match_pos) {
    int best_match_len = 0;

    int key = hash32(buf[pos] | (buf[pos + 1] << 8) | (buf[pos + 2] << 16)) & window_mask_;
    int64_t next = ht_[key];

    int64_t min_pos = pos - window_size_;
    int hits = 0;
    // Limit the number of hash buckets we search, otherwise the search can blow up
    // for larger window sizes.
    const int kNumHits = 16;
    const int kMinLength = 4;
    while (next > min_pos && ++hits < kNumHits) {
      int match_len = matchLength(&buf[pos], &buf[next], buf_end);
      if (match_len > best_match_len && match_len > kMinLength) {
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

uint8_t* writeVarint(uint8_t* buf, int v) {
  while (v > 0x7f) {
    *buf++ = 0x80 | (v & 0x7f);
  }
  *buf++ = v;
  return buf;
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

class LzEncoder {
public:
  // Initializes encoder with a backwards window of `window_size`.  Must be a power of 2!
  LzEncoder(int64_t window_size)
   : matcher_(window_size) {
  }

  // Compresses `buffer` from `buffer+p` to `buffer+p_end`.
  // Writes compressed sequence to `out`.  `out` must contain at least `window_size` bytes!
  // Returns number of bytes written to `out`.
  int64_t encode(uint8_t* buffer, int64_t p, int64_t p_end, uint8_t* out) {
    std::vector<int> match_offsets;
    std::vector<int> match_lengths;
    std::vector<int> literal_lengths;
    std::vector<uint8_t> literals;

    uint8_t* out_start = out;
    int num_literals = 0;

    for (int64_t i = p; i < p_end; ++i) {
      // Output a match?  Or a literal?
      int64_t match_pos;
      int match_len = matcher_.findMatch(buffer, buffer + p_end, i, match_pos);
      if (match_len != 0) {
        match_offsets.push_back(i - match_pos);
        match_lengths.push_back(match_len);
        literal_lengths.push_back(num_literals);
        num_literals = 0;

        // printf("Match cur:%lld, match:%lld len:%d\n", i, match_pos, match_len);
        /*
        printf("((");
        for (int j = 0; j < match_len; ++j) {
          printf("%c", buffer[i + j]);
        }
        printf("))");
        */

        while (--match_len > 0) {
          matcher_.insert(buffer, ++i);
        }
      } else {
        literals.push_back(buffer[i]);
        ++num_literals;
        // printf("%c", buffer[i]);
      }
    }
    if (num_literals != 0) {
      literal_lengths.push_back(num_literals);
      match_offsets.push_back(0);
      match_lengths.push_back(0);
    }

    // Write literal section
    {
      // Uncompressed length
      writeInt<3>(out, literals.size());
      out += 3;
      // Compressed length
      uint8_t* marker = out;
      out += 3;

      // Huffman table for literals
      HuffmanEncoder encoder(out);
      for (uint8_t literal : literals) {
        encoder.scan(literal);
      }
      encoder.buildTable();
      for (uint8_t literal : literals) {
        encoder.encode(literal);
      }
      int64_t bytes_written = encoder.finish();
      out += bytes_written;
      writeInt<3>(marker, bytes_written);
      LOGV(1, "literals: %lu -> %lld\n", literals.size(), bytes_written);
    }

    // Write sequences section
    writeInt<3>(out, literal_lengths.size());
    out += 3;

    /*
    for (int i = 0; i < literal_lengths.size(); ++i) {
      LOGV(2, "Encoding (lit_len:%d, match_offset:%d, match_length:%d)\n", literal_lengths[i], match_offsets[i], match_lengths[i]);
    }
    */

    // a. Literal lengths
    int lit_len_out = writeValues(out, literal_lengths);
    out += lit_len_out;
    // b. Match offsets
    int match_offsets_out = writeValues(out, match_offsets);
    out += match_offsets_out;
    // c. Match lengths
    int match_lengths_out = writeValues(out, match_lengths);
    out += match_lengths_out;

    LOGV(1, "Wrote block, %lu sequences lit_len:%d match_offsets:%d match_lengths:%d\n", literal_lengths.size(), lit_len_out, match_offsets_out, match_lengths_out);

    return out - out_start;
  }

private:
  int64_t writeValues(uint8_t* out, const std::vector<int>& values) {
    HuffmanEncoder encoder(out);
    for (int v : values) {
      encoder.scan(literalLengthCode(v));
    }
    encoder.buildTable();
    for (int v : values) {
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
};

class LzDecoder {
public:
  bool decode(uint8_t* buf, uint8_t* end, uint8_t* out, uint8_t* out_end) {
    uint8_t literals[1 << 18];
    int literal_lengths[1 << 16];
    int match_offsets[1 << 16];
    int match_lengths[1 << 16];

    {
      int num_literals = readInt<3>(buf);
      int compressed_size = readInt<3>(buf + 3);
      buf += 6;
      LOGV(1, "Read %d literals, %d compressed bytes\n", num_literals, compressed_size);

      HuffmanDecoder decoder(buf, buf + compressed_size);
      CHECK(decoder.readTable());
      CHECK(decoder.assignCodes());
      CHECK(decoder.decode(literals, literals + num_literals));
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
    HuffmanDecoder decoder(buf, end);
    CHECK(decoder.readTable());
    CHECK(decoder.assignCodes());
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
  LzEncoder lz_encoder(chunk_size);

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
  HuffmanEncoder encoder(out);
  for (int64_t i = 0; i < len; ++i) {
    encoder.scan(buf[i]);
  }
  encoder.buildTable();
  for (int64_t i = 0; i < len; ++i) {
    encoder.encode(buf[i]);
  }
  int64_t encoded_size = encoder.finish();
  // printf("Encoded %zu into %zu bytes\n", len, encoded_size);

  std::unique_ptr<uint8_t> decoded;
  decoded.reset(new uint8_t[len]);
  HuffmanDecoder decoder(out, out + encoded_size);
  CHECK(decoder.readTable());
  CHECK(decoder.assignCodes());
  CHECK(decoder.decode(decoded.get(), decoded.get() + len));

  return checkBytes(decoded.get(), buf, len) == 0;
}

/*
void huffmanSpeed() {
  int64_t len;
  std::unique_ptr<uint8_t> buf = enwik8(len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  int64_t encoded_size;
  {
    Timer timer;
    encoded_size = huffmanCompress(buf.get(), len, out.get());
    double elapsed = timer.elapsed() / 1000;
    printf("Encoded %lld into %lld bytes\n", len, encoded_size);
    printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);
  }

  {
    Timer timer;
    decompress(out.get(), encoded_size, buf.get(), len);
    double elapsed = timer.elapsed() / 1000;
    printf("Decompression\n");
    printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);
  }
  {
    std::unique_ptr<uint8_t> truth = enwik8(len);
    for (int i = 0; i < len; ++i) {
      CHECK(truth.get()[i] == buf.get()[i]);
    }
    printf("Decompression validated!\n");
  }
}
*/

void testLz() {
  int64_t len;
  std::unique_ptr<uint8_t> enwik8 = readEnwik8(len);
  // len = 10000000;
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

int main() {
  /*
  int64_t len;
  std::unique_ptr<uint8_t> buf = enwik8(len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  testBitReader(buf.get(), out.get(), 1000);
  for (int i = 1; i < 1000; i += 50) {
    CHECK(testHuffman(buf.get(), out.get(), i));
  }
  */

  testLz();

  return 0;
}
