"""Check the [18,3,16] Euclidean self-orthogonal MDS code over F16.

Uses polynomial multiplication followed by long division modulo X^4+X+1.
No external dependencies. Run with python verify_liu16.py.
"""
from collections import Counter
from itertools import combinations, product

COLUMNS = (
    (15, 0, 0),
    (13, 13, 13),
    (5, 10, 2),
    (9, 8, 2),
    (2, 8, 12),
    (1, 5, 7),
    (1, 6, 2),
    (1, 7, 3),
    (12, 10, 13),
    (1, 9, 10),
    (1, 10, 12),
    (1, 11, 13),
    (1, 12, 9),
    (1, 13, 8),
    (1, 14, 15),
    (1, 15, 14),
    (0, 1, 0),
    (0, 0, 1),
)


def mul(a, b):
    value = 0
    for bit in range(4):
        if (b >> bit) & 1:
            value ^= a << bit
    for degree in range(6, 3, -1):
        if (value >> degree) & 1:
            value ^= 0b10011 << (degree - 4)
    return value


def dot(left, right):
    value = 0
    for a, b in zip(left, right):
        value ^= mul(a, b)
    return value


def determinant(a, b, c):
    return (
        mul(a[0], mul(b[1], c[2]) ^ mul(b[2], c[1]))
        ^ mul(a[1], mul(b[0], c[2]) ^ mul(b[2], c[0]))
        ^ mul(a[2], mul(b[0], c[1]) ^ mul(b[1], c[0]))
    )


def main():
    # Independently reconstruct the published Lunelli-Sce projective points.
    def power(a, exponent):
        value = 1
        for _ in range(exponent):
            value = mul(value, a)
        return value

    def f(t):
        return (
            power(t, 12) ^ power(t, 10) ^ mul(power(2, 11), power(t, 8))
            ^ power(t, 6) ^ mul(power(2, 2), power(t, 4))
            ^ mul(power(2, 9), power(t, 2))
        )

    scales = (15, 13, 5, 9, 2, 1, 1, 1, 12, 1, 1, 1, 1, 1, 1, 1)
    finite = tuple(
        (s, mul(s, t), mul(s, f(t))) for t, s in enumerate(scales)
    )
    assert COLUMNS == finite + ((0, 1, 0), (0, 0, 1))
    rows = tuple(zip(*COLUMNS))
    gram = tuple(tuple(dot(a, b) for b in rows) for a in rows)
    assert gram == ((0, 0, 0),) * 3
    minors = [determinant(a, b, c) for a, b, c in combinations(COLUMNS, 3)]
    assert len(minors) == 816 and all(minors)

    weights = Counter(
        sum(dot(message, column) != 0 for column in COLUMNS)
        for message in product(range(16), repeat=3)
    )
    assert weights == {0: 1, 16: 2295, 18: 1800}
    print("F16 Gram matrix:", gram)
    print("Nonzero 3x3 minors:", len(minors))
    print("All 4096 messages, weight counts:", dict(sorted(weights.items())))


if __name__ == "__main__":
    main()
