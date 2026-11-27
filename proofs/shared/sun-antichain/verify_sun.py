"""Finite cross-checks of Sun's two third conjectures. Uses the standard library.

The proof for arbitrarily large counterexamples is in SunAntichain.lean.
This program builds the original summands k**a + m**c directly.
"""


def powers_below(base, upper):
    value = 1
    while value <= upper:
        yield value
        value *= base


def possible_terms(k, m, upper):
    return sorted({
        x + y
        for x in powers_below(k, upper)
        for y in powers_below(m, upper - x)
    })


def antichain_sums(terms, upper):
    """Exact sums for the actual pairwise nondivisibility condition."""
    sums = set()

    def extend(first, chosen, total):
        sums.add(total)
        for index in range(first, len(terms)):
            value = terms[index]
            if value + total > upper:
                break
            if all(value % smaller != 0 for smaller in chosen):
                extend(index + 1, chosen + [value], value + total)

    extend(0, [], 0)
    return sums


def groups_by_gap(terms, base):
    """Recover each exponent gap from the numerical value of a summand."""
    groups = {}
    for value in terms:
        cofactor = value
        while cofactor % base == 0:
            cofactor //= base
        power = cofactor - 1
        gap = 0
        while power > 1 and power % base == 0:
            power //= base
            gap += 1
        assert power == 1
        groups.setdefault(gap, []).append(value)
    return groups


def relaxed_sums(groups, upper):
    """Bit i records representability by at most one summand per gap."""
    bits = 1
    mask = (1 << (upper + 1)) - 1
    for vals in groups.values():
        before = bits
        for v in vals:
            bits |= before << v
        bits &= mask
    return bits


def check(base, length):
    target = base ** length - 1
    terms = possible_terms(base, base * base, target)
    groups = groups_by_gap(terms, base)
    assert all(gap < length for gap in groups)
    for vals in groups.values():
        assert all(y % x == 0 for x in vals for y in vals if x < y)
    relaxed = relaxed_sums(groups, target)
    assert not ((relaxed >> target) & 1)
    if length <= 4:
        exact = antichain_sums(terms, target)
        assert target not in exact
        assert all((relaxed >> v) & 1 for v in exact)
    print(f"bases ({base}, {base**2}), L={length}, missing {target}, "
          f"{len(terms)} candidate summands in {len(groups)} gap groups")


if __name__ == "__main__":
    for base in (4, 5):
        for length in range(1, 8):
            check(base, length)
