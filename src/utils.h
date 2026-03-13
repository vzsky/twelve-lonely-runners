#pragma once 

#include <algorithm>
#include <cassert>
#include <chrono>
#include <climits>
#include <cstdint>
#include <functional>
#include <iostream>
#include <numeric>
#include <thread>
#include <utility>
#include <vector>

inline size_t parallelize_core()
{
  unsigned int hw = std::thread::hardware_concurrency();
  return hw ? hw : 4u;
}

// Fallback GCD for subset-gcd checking (used in sieve condition)
template <typename T> inline T gcd_fallback(T a, T b)
{
  a = std::abs(a);
  b = std::abs(b);
  while (b)
  {
    long long t = b;
    b           = a % b;
    a           = t;
  }
  return a;
}

template <typename T, typename... Ts> inline T gcd_fallback(T a, T b, Ts... rest)
{
  return gcd_fallback(gcd_fallback(a, b), rest...);
}

inline std::string print_time()
{
  auto now = std::chrono::system_clock::now();
  return std::format("{:%H:%M:%S}", now);
}

template <typename Func> auto timeit(Func&& f)
{
  using namespace std::chrono;
  auto start = high_resolution_clock::now();

  f();

  auto end      = high_resolution_clock::now();
  auto duration = duration_cast<milliseconds>(end - start).count();
  std::cout << "Time elapsed: " << duration / 1000 << "." << duration % 1000 << "s" << std::endl;
}
