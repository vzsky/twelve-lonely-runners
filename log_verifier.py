#!/usr/bin/env python3
import re
import math
import sys

def is_primes_enough(primes, k):
    uniq_primes = sorted(set(primes))
    if len(uniq_primes) != len(primes):
        print("WARNING: Prime in list is not unique")

    s = sum(math.log(p) for p in uniq_primes)

    binom = k * (k + 1) / 2.0
    base = (binom ** (k - 1)) / k
    tres = k * math.log(base)

    return s > tres, s, tres


def parse_log(path):
    primes = []
    k = None

    re_params = re.compile(r"Parameters:\s*p\s*=\s*(\d+),\s*k\s*=\s*(\d+)")
    re_zero = re.compile(r"S size\s*=\s*0")

    current_p = None
    saw_zero = False

    with open(path, "r") as f:
        for line in f:
            m = re_params.search(line)
            if m:
                if current_p is not None and saw_zero:
                    primes.append(current_p)

                current_p = int(m.group(1))
                k = int(m.group(2))
                saw_zero = False
                continue

            if current_p is not None and re_zero.search(line):
                saw_zero = True

        if current_p is not None and saw_zero:
            primes.append(current_p)

    if k is None:
        raise RuntimeError("No parameters found in log")

    return primes, k


def main():
    if len(sys.argv) != 2:
        print("usage: python check_proof.py <logfile>")
        sys.exit(1)

    primes, k = parse_log(sys.argv[1])
    ok, s, tres = is_primes_enough(primes, k)

    print(f"k = {k}")
    print(f"valid primes = {primes}")
    print(f"log prod(primes) = {s}")
    print(f"log threshold    = {tres}")
    print("PROOF:", "YES" if ok else "NO")


if __name__ == "__main__":
    main()
