"""Check Bala's two OEIS specializations and the general coefficient expansion."""
from fractions import Fraction
from math import comb, factorial


def multiply(f, g, n):
    return [sum(f[i] * g[j - i] for i in range(j + 1)) for j in range(n + 1)]


def gpowers(g, n):
    powers = [[1] + [0] * n]
    for _ in range(n):
        powers.append(multiply(powers[-1], g, n))
    return powers


def direct(f, g, n):
    # Compute E = exp(x*G^n) by solving E' = (x*G^n)' E coefficientwise.
    exponent = [0] + gpowers(g, n)[n][:-1]
    e = [Fraction(1)]
    for m in range(1, n + 1):
        e.append(sum(i * exponent[i] * e[m - i] for i in range(1, m + 1)) / m)
    value = factorial(n) * multiply(f, e, n)[n]
    assert value.denominator == 1
    return value.numerator


def expanded(f, g, n):
    h = list(g[: n + 1])
    h[0] -= 1
    rows = [multiply(f, p, n) for p in gpowers(h, n)]
    return sum(
        rows[i][j] * (factorial(n) // factorial(n - j)) * comb(n * (n - j), i)
        for j in range(n + 1) for i in range(j + 1)
    )


def main():
    nmax = 18
    one = [1] + [0] * nmax
    linear = [1, 1] + [0] * (nmax - 1)
    tests = [
        ("A293013", one, [1] * (nmax + 1), [1, 1, 5, 55, 961, 24101, 818821]),
        ("A361281", one, linear, [1, 1, 5, 37, 481, 10001, 288901]),
        ("sharpness", [0, 1] + [0] * (nmax - 1), one, list(range(nmax + 1))),
        ("signed series", [(-1)**j * (j + 2) for j in range(nmax + 1)],
         [1] + [(-1)**j * j for j in range(1, nmax + 1)], []),
    ]
    for label, f, g, prefix in tests:
        seq = [direct(f, g, n) for n in range(nmax + 1)]
        assert seq == [expanded(f, g, n) for n in range(nmax + 1)]
        assert seq[: len(prefix)] == prefix
        for k in range(1, nmax + 1):
            assert all((seq[n + k] - seq[n]) % k == 0 for n in range(nmax + 1 - k))
        print(f"{label}: direct coefficients, binomial expansion and all shifts through {nmax} passed")


if __name__ == "__main__":
    main()
