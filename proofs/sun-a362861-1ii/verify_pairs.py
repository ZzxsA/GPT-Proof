"""Check the odd-base classification independently by finite subset sums."""

from itertools import combinations_with_replacement

MAX_TARGET = 4096


def powers(base, exponent_limit=None):
    values = []
    value = 1
    while value < MAX_TARGET and (exponent_limit is None or len(values) <= exponent_limit):
        values.append(value)
        value *= base
    return values


def first_missing_even(k, m, exponent_limit=None):
    terms = {x + y for x in powers(k) for y in powers(m, exponent_limit) if x + y <= MAX_TARGET}
    bits = 1
    mask = (1 << (MAX_TARGET + 1)) - 1
    for term in sorted(terms):
        bits = (bits | (bits << term)) & mask
    return next((n for n in range(2, MAX_TARGET + 1, 2) if not (bits >> n) & 1), None)


def main():
    pairs = list(combinations_with_replacement(range(3, 32, 2), 2))
    for k, m in pairs:
        expected = 4 if k >= 5 else (8 if m >= 9 else None)
        assert first_missing_even(k, m) == expected, (k, m)
    for q in (3, 5, 7):
        assert first_missing_even(3, q, 1) is None
        assert first_missing_even(3, q, 0) == 8
    print(f"Checked all even targets through {MAX_TARGET} for {len(pairs)} unordered base pairs.")
    print("For q=3,5,7, exponents 0 and 1 suffice over that range; exponent 0 alone misses 8.")


if __name__ == "__main__":
    main()
