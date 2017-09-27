#include <algorithm>
#include <cstdio>
#include <cstdlib>
#include <cstdint>
#include <queue>
#include <string>
#include <vector>

#define CHECK(cond) do{if(!(cond)){fprintf(stderr,"%s:%d CHECK %s\n", __FILE__, __LINE__, #cond);exit(1);}}while(0);

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

int log2RoundUp(uint32_t v) {
  if (v > 1) {
    return 32 - __builtin_clz(v - 1);
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

  bool done() const {
    return current_ >= end_ && position_ == 0;
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

  size_t finish() {
    flush();
    CHECK(position_ >= 0 && position_ < 8);
    if (position_ > 0) {
      // Final byte is a bit tricky.  Handle it specially.
      *current_ = (bits_ & ((1 << position_) - 1)) << (8 - position_);
      ++current_;
    }
    return current_ - start_;
  }

private:
  void flush() {
    while (position_ >= 8) {
      *current_ = (bits_ >> (position_ - 8)) & 0xFF;
      position_ -= 8;
      ++current_;
    }
  }

private:
  uint8_t* start_;
  uint8_t* current_;
  uint32_t bits_ = 0;
  int position_ = 0;
};

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
  HuffmanEncoder(uint8_t* buffer, size_t buf_size, int target_size)
    : buffer_(buffer),
      writer_(buffer_),
      buf_size_(buf_size),
      target_size_(target_size) {
    for (int i = 0; i < 256; ++i) {
      freq_[i].symbol = i;
    }
  }

  void scan(int symbol) {
    ++freq_[symbol].freq;
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

    walk(q.top(), 0);

    // TODO: Not efficient...
    std::sort(&freq_[0], &freq_[256], [](const Node& l, const Node& r){return l.freq < r.freq;});

    writer_.writeBits(num_symbols, 8);
    writer_.writeBits(4, 3);

    int code = 0;
    int last_level = -1;
    for (int i = 0; i < num_symbols; ++i) {
      CHECK(freq_[i].freq != kSentinel);
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

      // printf("code:%s hex:%x level:%d symbol:%d\n", toBinary(code, level).c_str(), code, level, freq_[i].symbol);
    }
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

  size_t finish() {
    return writer_.finish();
  }

private:
  uint8_t* buffer_;
  BitWriter writer_;
  size_t at_ = 0;
  size_t buf_size_;
  int target_size_;

  Node freq_[512] = {0};

  uint8_t length_[256] = {0};
  int code_[256] = {0};
};

class HuffmanDecoder {
public:
  HuffmanDecoder(uint8_t* buffer, uint8_t* end, uint8_t* output)
    : br_(buffer, end),
      output_(output) {
  }

  bool readTable() {
    int sym_bits = 8;

    br_.refill();
    num_symbols_ = br_.readBits(sym_bits);

    CHECK(num_symbols_ <= kMaxSymbols);

    int codelen_bits = br_.readBits(3);
    printf("num_sym %d codelen_bits %d\n", num_symbols_, codelen_bits);
    for (int i = 0; i < num_symbols_; ++i) {
      br_.refill();
      int symbol = br_.readBits(sym_bits);
      int codelen = br_.readBits(codelen_bits) + 1;

      ++codelen_count_[codelen];
      last_used_symbol_ = symbol;
      symbol_length_[i] = codelen;
      symbol_[i] = symbol;
      min_codelen_ = std::min(min_codelen_, codelen);
      max_codelen_ = std::max(max_codelen_, codelen);
    }

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

  bool decode() {
    br_.refill();
    int bits = br_.readBits(10);
    int bitpos = 0;
    for (;;) {
      int n = bits & 0x3ff;
      int len = bits_to_len_[n];
      *output_++ = bits_to_sym_[n];
      bits <<= len;
      br_.refill();
      bits |= br_.readBits(len);
      if (br_.done()) {
        break;
      }
    }
    return true;
  }

private:
  static const int kMaxSymbols = 256;
  static const int kMaxCodeLength = 11;

  BitReader br_;
  uint8_t* output_;
  int num_symbols_;
  int last_used_symbol_;
  int min_codelen_ = 255;
  int max_codelen_ = 0;
  int codelen_count_[17] = {0};
  uint8_t symbol_length_[kMaxSymbols] = {0}; 

  uint8_t symbol_[256] = {0};
  uint8_t bits_to_sym_[0x7ff] = {0};
  uint8_t bits_to_len_[0x7ff] = {0};
};

void compress() {
}

void decompress() {
  // read compressed 256kb chunk
}

std::unique_ptr<uint8_t> enwik8(size_t& len) {
  FILE* f = fopen("enwik8", "r");
  fseek(f, 0, SEEK_END);
  len = ftell(f);
  fseek(f, 0, SEEK_SET);

  std::unique_ptr<uint8_t> buf;
  buf.reset(new uint8_t[len]);
  fread(buf.get(), 1, len, f);
  return std::move(buf);
}

int testBitReader(uint8_t* buf, uint8_t* out, size_t len) {
  BitReader orig_reader(buf, buf + len);
  BitWriter writer(out);
  for (size_t i = 0; i < 8 * len; ++i) {
    orig_reader.refill();
    writer.writeBit(orig_reader.readBit());
  }

  BitReader reader(out, out + len);
  for (size_t i = 0; i < len; ++i) {
    reader.refill();
    uint8_t orig = buf[i];
    uint8_t written = reader.readBits(8);
    if (orig != written) {
      fprintf(stderr, "busted %ld,%d,%d\n", i, orig, written);
      return 1;
    }
  }

  return 0;
}

int testHuffman(uint8_t* buf, uint8_t* out, size_t len) {
  HuffmanEncoder encoder(out, 256 * 1024, 0);
  for (size_t i = 0; i < len; ++i) {
    encoder.scan(buf[i]);
  }
  encoder.buildTable();
  for (size_t i = 0; i < len; ++i) {
    encoder.encode(buf[i]);
  }
  size_t encoded_size = encoder.finish();
  printf("Encoded into %zu bytes\n", encoded_size);

  uint8_t decoded[len];
  HuffmanDecoder decoder(out, out + encoded_size, decoded);
  CHECK(decoder.readTable());
  CHECK(decoder.assignCodes());
  CHECK(decoder.decode());

  for (size_t i = 0; i < len; ++i) {
    uint8_t orig = buf[i];
    uint8_t v = decoded[i];
    if (orig != v) {
      fprintf(stderr, "busted_huff %ld,%d,%d\n", i, orig, v);
    }
  }

  return 0;
}

int main() {
  size_t len;
  std::unique_ptr<uint8_t> buf = enwik8(len);
  printf("Read %ld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  testBitReader(buf.get(), out.get(), 1000);
  testHuffman(buf.get(), out.get(), 1000);

  return 0;
}
