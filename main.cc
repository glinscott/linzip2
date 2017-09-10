#include <algorithm>
#include <cstdio>
#include <cstdint>
#include <vector>

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
    while (position_ > 0) {
      bits_ |= (current_ < end_ ? *current_ : 0) << position_;
      position_ -= 8;
      ++current_;
    }
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
    : current_(buffer) {
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

  void flush() {
    while (position_ > 0) {
      *current_ = (bits_ >> (position_ - 8)) & 0xFF;
      position_ -= 8;
      ++current_;
    }
  }

private:
  uint8_t* current_;
  uint32_t bits_ = 0;
  int position_ = 0;
};

class HuffmanDecoder {
public:
  HuffmanDecoder(uint8_t* buffer, uint8_t* end)
    : br_(buffer, end) {
  }

  bool readTable() {
    int sym_bits = log2RoundUp(num_symbols_);

    br_.refill();
    num_symbols_ = br_.readBits(sym_bits);

    if (num_symbols_ > kMaxSymbols) {
      return false;
    }

    int codelen_bits = br_.readBits(3);
    for (int i = 0; i < num_symbols_; ++i) {
      br_.refill();
      int symbol = br_.readBits(sym_bits);
      int codelen = br_.readBits(codelen_bits) + 1;

      ++codelen_count_[codelen];
      last_used_symbol_ = symbol;
      symbol_length_[symbol] = codelen;
      min_codelen_ = std::min(min_codelen_, codelen);
      max_codelen_ = std::max(max_codelen_, codelen);
    }

    return true;
  }

  bool assignCodes() {
    int local_syms[17] = {0};
    int x = 0;
    int y = 0;
    int z = 0;
    for (int i = min_codelen_; i <= max_codelen_; ++i) {
      local_syms[i] = x;
      z = codelen_count_[i] + y;
      // int g_i = y - x;
      // int f_i = z << (32 - i);
      y = 2 * z;
      x += codelen_count_[i];
    }
    if (z != (1 << max_codelen_)) {
      return false;
    }
    uint8_t* C;
    for (int i = 0; i < last_used_symbol_ + 1; i++) {
      C[local_syms[symbol_length_[i]]++] = i;
    }
    return true;
  }

private:
  static const int kMaxSymbols = 256;
  static const int kMaxCodeLength = 11;

  BitReader br_;
  int num_symbols_;
  int last_used_symbol_;
  int min_codelen_ = 255;
  int max_codelen_ = 0;
  int codelen_count_[17] = {0};
  uint8_t symbol_length_[kMaxSymbols] = {0}; 
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

int main() {
  size_t len;
  std::unique_ptr<uint8_t> buf = enwik8(len);
  printf("Read %ld bytes\n", len);
  std::unique_ptr<uint8_t> out;
  out.reset(new uint8_t[len]);

  testBitReader(buf.get(), out.get(), 1000);

  return 0;
}
