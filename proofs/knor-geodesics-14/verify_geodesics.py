"""Count shortest paths directly in the two graphs from Problem 14."""

from collections import deque


def layer_graph(sizes):
    """Join consecutive independent sets in an undirected simple graph."""
    adj = [[] for _ in range(sum(sizes))]
    previous = range(0)
    first = 0
    for size in sizes:
        layer = range(first, first + size)
        for u in previous:
            for v in layer:
                adj[u].append(v)
                adj[v].append(u)
        previous = layer
        first += size
    return adj


def geodesic_count(adj):
    """Count unordered shortest paths, including all singleton paths."""
    total = 0
    for source in range(len(adj)):
        distance = [-1] * len(adj)
        ways = [0] * len(adj)
        distance[source] = 0
        ways[source] = 1
        queue = deque([source])
        while queue:
            u = queue.popleft()
            for v in adj[u]:
                if distance[v] == -1:
                    distance[v] = distance[u] + 1
                    queue.append(v)
                if distance[v] == distance[u] + 1:
                    ways[v] += ways[u]
        assert -1 not in distance
        total += sum(ways[source:])
    return total


def verify():
    for m in range(1, 21):
        uniform = geodesic_count(layer_graph([3] * (m + 2)))
        capped = geodesic_count(layer_graph([1, 2] + [3] * m + [2, 1]))
        power = 3**m
        assert 4 * uniform == 81 * power + 66 * m + 51
        assert 4 * capped == 121 * power + 66 * m - 9
        assert capped - uniform == 10 * power - 15 > 0
        assert capped >= 25 * power
        print(f"order {3 * m + 6:2}, uniform {uniform}, capped {capped}")


if __name__ == "__main__":
    verify()
