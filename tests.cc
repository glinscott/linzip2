#define LINZIP_LIBRARY_ONLY
#include "main.cc"

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

  std::unique_ptr<uint8_t> decoded(new uint8_t[len]);
  HuffmanDecoder decoder(out, out + encoded_size);
  decoder.readTable();
  decoder.decode(decoded.get(), decoded.get() + len);

  return checkBytes(decoded.get(), buf, len) == 0;
}

void huffmanSpeed() {
  int64_t len;
  std::unique_ptr<uint8_t> buf = readFile(kDefaultInputPath, len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out(new uint8_t[len]);

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
    std::unique_ptr<uint8_t> truth = readFile(kDefaultInputPath, len);
    for (int i = 0; i < len; ++i) {
      CHECK(truth.get()[i] == buf.get()[i]);
    }
    printf("Decompression validated!\n");
  }
}

void tuneSettings() {
  int64_t len;
  std::unique_ptr<uint8_t> input = readFile(kDefaultInputPath, len);
  uint8_t* buf = input.get();
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out(new uint8_t[len]);

  for (int level = 0; level <= 1; ++level) {
    for (int window_size = 26; window_size <= 26; window_size += 4) {
      for (int matches = 16; matches <= 16; matches += 2) {
        FLAG_level = level;
        FLAG_window_size = window_size;
        FLAG_max_matches = matches;

        Timer timer;
        int64_t encoded_size = lzCompress(buf, len, out.get());
        double elapsed = timer.elapsed() / 1000;
        printf("level:%d, window:%d, matches:%d, %lld bytes, %.2lf seconds, %.2lf MB/s\n",
               level, window_size, matches, encoded_size, elapsed,
               (len / (1024. * 1024.)) / elapsed);
      }
    }
  }
}

void testLz() {
  int64_t len;
  std::unique_ptr<uint8_t> input = readFile(kDefaultInputPath, len);
  uint8_t* buf = input.get();
  len = std::min<int64_t>(len, kLocalExperimentBytes);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out(new uint8_t[len + 512]);

  Timer timer;
  int64_t encoded_size = lzCompress(buf, len, out.get());
  printf("Encoded %lld into %lld bytes\n", len, encoded_size);
  double elapsed = timer.elapsed() / 1000;
  printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);

  std::unique_ptr<uint8_t> decoded(new uint8_t[len]);
  timer = Timer();
  lzDecompress(out.get(), encoded_size, decoded.get(), len);
  elapsed = timer.elapsed() / 1000;
  printf("%.2lf seconds, %.2lf MB/s\n", elapsed, (len / (1024. * 1024.)) / elapsed);

  CHECK(checkBytes(decoded.get(), buf, len) == 0);
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
    std::unique_ptr<uint8_t> out(new uint8_t[100 + len]);
    int64_t encoded_size = huffmanCompress(buf, len, out.get());
    std::unique_ptr<uint8_t> decoded(new uint8_t[len]);
    huffmanDecompress(out.get(), encoded_size, decoded.get(), len);
    CHECK(checkBytes(decoded.get(), buf, len) == 0);
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
    int out_size = 512 + len;
    std::unique_ptr<uint8_t> out(new uint8_t[out_size]);
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

    std::unique_ptr<uint8_t> decoded(new uint8_t[len]);
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
  std::unique_ptr<uint8_t> buf = readFile(kDefaultInputPath, len);
  printf("Read %lld bytes\n", len);
  std::unique_ptr<uint8_t> out(new uint8_t[len]);

  CHECK(testBitReader(buf.get(), out.get(), 1000) == 0);
  for (int i = 1; i < 1000; i += 50) {
    CHECK(testHuffman(buf.get(), out.get(), i));
  }
  testShort();
  testFSEEncoder();
  testLz();
}

int main() {
  tests();
  return 0;
}
