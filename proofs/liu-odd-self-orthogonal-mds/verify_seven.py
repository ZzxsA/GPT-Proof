"""Independently enumerate the normalized candidate MDS codes over GF(7)."""
from itertools import combinations, permutations, product


def determinant(a, b, c):
    return (
        a[0] * (b[1]*c[2] - b[2]*c[1])
        - a[1] * (b[0]*c[2] - b[2]*c[0])
        + a[2] * (b[0]*c[1] - b[1]*c[0])
    ) % 7


def main():
    squares = tuple(sorted({a*a % 7 for a in range(1, 7)}))
    arcs = []
    checked = hits = 0
    for ys in permutations(range(2, 7)):
        order = (1,) + ys
        cols = [(1, x, y) for x, y in enumerate(order, start=1)] + [(0,1,0), (0,0,1)]
        if not all(determinant(*triple) for triple in combinations(cols, 3)):
            continue
        arcs.append(order)
        for weights in product(squares, repeat=8):
            checked += 1
            if all(sum(w*c[i]*c[j] for w,c in zip(weights, cols)) % 7 == 0
                   for i in range(3) for j in range(i, 3)):
                hits += 1
    assert arcs == [(1,4,5,2,3,6)]
    assert checked == 3**8 and hits == 0
    print("120 affine permutations; one arc; 6561 square-multiplier tuples; zero self-orthogonal codes.")


if __name__ == "__main__":
    main()
