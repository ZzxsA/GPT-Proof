"""Exhaust the ternary MDS codes and the normalized order-five arcs."""

from itertools import combinations, product


def ternary_codes(k):
    n = 4
    # The first k coordinates form an information set for every MDS code.
    for tail in product(range(3), repeat=k * (n - k)):
        rows = [
            [int(i == j) for j in range(k)] + list(tail[i * (n-k):(i+1) * (n-k)])
            for i in range(k)
        ]
        words = frozenset(
            tuple(sum(a * x for a, x in zip(message, col)) % 3 for col in zip(*rows))
            for message in product(range(3), repeat=k)
        )
        if min(sum(x != 0 for x in w) for w in words if any(w)) == n-k+1:
            yield words


def determinant_mod_5(p, q, r):
    return sum(p[i] * (q[(i+1)%3] * r[(i+2)%3] - q[(i+2)%3] * r[(i+1)%3])
               for i in range(3)) % 5


def check_projective_model():
    # The first three projective points are the coordinate axes, the fourth
    # is (1,1,1), and the remaining points may all be normalized to z=1.
    fixed = [(1,0,0), (0,1,0), (0,0,1), (1,1,1)]
    survivors = 0
    for a,b,c,d,e,f in product(range(5), repeat=6):
        points = fixed + [(a,b,1), (c,d,1), (e,f,1)]
        survivors += all(determinant_mod_5(*triple) for triple in combinations(points, 3))
    return survivors


if __name__ == '__main__':
    small, large = list(ternary_codes(2)), list(ternary_codes(3))
    nested = sum(c <= d for c in small for d in large)
    print(f'Ternary [4,2,3] codes: {len(small)}; [4,3,2] codes: {len(large)}; nested pairs: {nested}')
    assert len(small) > 0 and len(large) > 0 and nested == 0
    arcs = check_projective_model()
    print(f'Normalized ordered 7-arcs in PG(2,5): {arcs}')
    assert arcs == 0
