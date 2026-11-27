"""Verify the base-five seed of OEIS A362861 by exhaustive subset enumeration."""

from itertools import combinations


HOLES = (2, 7, 10, 11, 12, 27, 35, 50, 51, 52, 55, 60, 135, 255)


def half_term(a, j):
    return (5**a + 5**j) // 2


def main():
    coins = [half_term(a, j) for a in range(5) for j in range(a + 1)]
    assert len(coins) == len(set(coins)) == 15
    assert sum(coins) == 2343 and half_term(5, 0) == 1563
    reachable = {
        sum(picked)
        for size in range(len(coins) + 1)
        for picked in combinations(coins, size)
    }
    assert tuple(n for n in range(2088) if n not in reachable) == HOLES
    assert 2088 not in reachable
    assert len(reachable) == 2344 - 2 * len(HOLES)
    # Check the first few transitions of the general interval induction.
    upper = 2087
    for a in range(5, 20):
        assert half_term(a, 0) <= upper - 256 + 1
        for j in range(4):
            coin = half_term(a, j)
            assert coin <= upper - 256 + 1
            upper += coin
        assert half_term(a + 1, 0) <= upper - 256 + 1
    print(f"Checked all {1 << len(coins)} subsets of {coins}.")
    print(f"The only omissions in [0, 2087] are {list(HOLES)}.")
    print("The consecutive interval [256, 2087] has length 1832.")


if __name__ == "__main__":
    main()
