"""Cross-check same-rank Farey coincidences and common grid points exactly."""
from fractions import Fraction
from math import gcd


def check(order):
    farey = sorted({
        Fraction(a, d)
        for d in range(1, order + 1)
        for a in range(d + 1)
    })
    intervals = len(farey) - 1
    fixed = sum(
        intervals * fraction.numerator == i * fraction.denominator
        for i, fraction in enumerate(farey)
    )
    common = sum(intervals % fraction.denominator == 0 for fraction in farey)
    divisor_count = sum(intervals % d == 0 for d in range(1, intervals + 1))
    by_denominator = 1 + sum(
        sum(gcd(a, d) == 1 for a in range(d))
        for d in range(1, order + 1) if intervals % d == 0
    )
    assert fixed <= common == by_denominator <= 1 + order * divisor_count
    return fixed, common


if __name__ == "__main__":
    prefix = [
        2, 3, 3, 5, 5, 7, 5, 3, 9, 7, 9, 3, 3, 7, 17, 17, 
        15, 11, 13, 11, 19, 15, 5, 25, 21, 5, 11, 17, 25, 3, 7, 13, 
        5, 29, 27, 41, 35, 33, 7, 17, 7, 3, 5, 3, 3, 23, 17, 5, 
        19, 15, 25, 9, 35, 47, 29, 5, 31, 3, 7, 27, 9, 5, 5, 61, 
        5, 9, 23, 41, 51, 15, 29, 3, 9, 23, 31, 3, 7, 33, 3, 3
    ]
    for order, expected in enumerate(prefix, 1):
        assert check(order)[0] == expected, order
    assert check(5) == (5, 7)
    print(f"Checked {len(prefix)} published counts, all ranks and both bounds.")
