from fractions import Fraction
from math import prod


def resultant(f, g):
    if len(g) == 1:
        return g[0] ** (len(f) - 1)
    a = len(f) - 1
    b = len(g) - 1
    r = list(f)
    while len(r) >= len(g):
        shift = len(r) - len(g)
        scale = r[-1] / g[-1]
        for i, coeff in enumerate(g):
            r[i + shift] -= coeff * scale
        while r and r[-1] == 0:
            r.pop()
    if not r:
        return 0
    return (-1)**(a*b) * g[-1]**(a-len(r)+1) * resultant(g, r)


def divisors(num):
    result = set()
    d = 2
    while d*d <= num:
        while num % d == 0:
            result.add(d)
            num //= d
        d += 1
    if num > 1:
        result.add(num)
    return result


def check(n):
    exponents = range(2, n)
    factors = set()
    for t in exponents:
        f = [Fraction(1)] * n
        g = list(map(Fraction, [2, -1] + [0] * (t-2) + [-1]))
        norm = abs(resultant(f, g))
        assert norm.denominator == 1 and norm != 0
        factors.update(p for p in divisors(norm.numerator) if (p-1) % n == 0)
    # For these primes Φ_n splits; every zero resultant implies a collision.
    print(n, sorted(factors), prod(factors))
    return max(factors), prod(factors)


if __name__ == '__main__':
    for n in (5,7,11,13,17,19,23):
        assert check(n)[0] == (2**n+1)//3
    assert check(29) == (108050869,23185169775494678703965601811862664516267203026525520380383050531459422153206071324389)
