"""Verify the prism directly, or enumerate smaller connected graphs using nauty geng."""

import argparse
from functools import lru_cache
from itertools import combinations
import subprocess


@lru_cache(maxsize=None)
def residue(degrees):
    work = list(degrees)
    while work and max(work):
        work.sort(reverse=True)
        degree = work.pop(0)
        for i in range(degree):
            work[i] -= 1
    return len(work)


def periphery_size(graph):
    eccentricities = []
    all_vertices = (1 << len(graph)) - 1
    for source in range(len(graph)):
        seen = frontier = 1 << source
        distance = 0
        while seen != all_vertices:
            neighbors = 0
            while frontier:
                vertex = frontier & -frontier
                neighbors |= graph[vertex.bit_length() - 1]
                frontier ^= vertex
            frontier = neighbors & ~seen
            if not frontier:
                raise ValueError("expected a connected graph")
            seen |= frontier
            distance += 1
        eccentricities.append(distance)
    return eccentricities.count(max(eccentricities))


def independent_sets(graph, choices, chosen=0):
    if not choices:
        yield chosen
        return
    vertex = choices & -choices
    options = choices ^ vertex
    yield from independent_sets(graph, options, chosen)
    yield from independent_sets(graph, options & ~graph[vertex.bit_length() - 1], chosen | vertex)


def check(graph):
    degrees = tuple(sorted(map(int.bit_count, graph), reverse=True))
    delta = degrees[0]
    r = residue(degrees)
    # No nonempty graph can violate the bound if at most one vertex is required.
    if len(graph) - delta - r <= 1:
        return None
    p = periphery_size(graph)
    if p - delta - r <= 1:
        return None
    alpha = 0
    for chosen in independent_sets(graph, (1 << len(graph)) - 1):
        size = chosen.bit_count()
        if size == 0:
            continue
        if size >= p - delta - r:
            return None
        neighborhood = 0
        rest = chosen
        while rest:
            bit = rest & -rest
            neighborhood |= graph[bit.bit_length() - 1]
            rest ^= bit
        if neighborhood.bit_count() <= size:
            return None
        alpha = max(alpha, size)
    return alpha, p, delta, r


def decode(line):
    values = [c - 63 for c in line.strip()]
    n = values[0]
    if not 0 < n < 63:
        raise ValueError("expected the short graph6 format")
    graph = [0] * n
    i = 0
    for v in range(1, n):
        for u in range(v):
            if values[1 + i // 6] & (1 << (5 - i % 6)):
                graph[u] |= 1 << v
                graph[v] |= 1 << u
            i += 1
    return graph


def prism(m):
    neighbors = [0] * (2 * m)
    for u, v in combinations(range(2 * m), 2):
        if u // m == v // m or u % m == v % m:
            neighbors[u] |= 1 << v
            neighbors[v] |= 1 << u
    return neighbors


def census(geng):
    expected_counts = (1, 1, 2, 6, 21, 112, 853, 11117, 261080)
    for n, expected in enumerate(expected_counts, start=1):
        counts = 0
        hits = []
        with subprocess.Popen([geng, "-cq", str(n)], stdout=subprocess.PIPE) as process:
            for line in process.stdout:
                counts += 1
                witness = check(decode(line))
                if witness:
                    hits.append((line.strip().decode("ascii"), witness))
            if process.wait() != 0:
                raise RuntimeError("geng failed")
        print(f"order {n}: {counts} connected graphs, {len(hits)} violations", flush=True)
        if counts != expected or hits:
            raise AssertionError((n, expected, counts, hits[:3]))


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--census", metavar="GENG", help="path to the nauty geng executable")
    args = parser.parse_args()
    model = prism(5)
    archived = decode(b"IJ]KlNF}?")
    archive_order = [0, 5, 6, 7, 8, 9, 4, 3, 2, 1]
    assert sorted(archive_order) == list(range(10))
    for u, v in combinations(range(10), 2):
        assert bool(model[u] & (1 << v)) == bool(archived[archive_order[u]] & (1 << archive_order[v]))
    witness = check(model)
    assert witness == (2, 10, 5, 2)
    print("K5 x K2: alpha = 2, periphery = 10, maximum degree = 5, residue = 2.", flush=True)
    if args.census:
        census(args.census)
