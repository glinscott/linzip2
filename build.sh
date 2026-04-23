#!/bin/bash

g++ --std=c++17 -O3 main.cc -o linzip
g++ --std=c++17 -O3 tests.cc -o linzip_tests
#g++ --std=c++11 -g -fsanitize=address main.cc -o linzip
