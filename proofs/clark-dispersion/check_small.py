"""Enumerate connected labelled graphs through order six and check the sharp bounds."""

import itertools
from math import sqrt

import numpy as np


def envelope(r):
    t = sqrt(r)
    return (1 - 1/r)**2 * (1 - (2*t/(t+1)**2)**2) / 4


def connected(adj):
    seen = {0}
    stack = [0]
    while stack:
        v = stack.pop()
        for w in np.flatnonzero(adj[v]):
            if w not in seen:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(adj)


def check(n):
    edges = list(itertools.combinations(range(n), 2))
    count = 0
    stars = 0
    max_value = float("-inf")
    for mask in range(1 << len(edges)):
        adj = np.zeros((n, n))
        for i, (u, v) in enumerate(edges):
            if mask >> i & 1:
                adj[u, v] = adj[v, u] = 1
        if not connected(adj):
            continue
        count += 1
        degree = adj.sum(axis=0)
        x = abs(np.linalg.eigh(adj)[1][:, -1])
        assert min(x) > 0
        c = np.var(degree)/np.mean(degree)**2
        e = np.var(x)/np.mean(x)**2
        r = max(degree)/min(degree)
        value = (c-e)/(max(x)/min(x))**2
        max_value = max(max_value, value)
        tol = 1e-10
        assert e + tol >= c/(1+sqrt(1+c))**2
        assert -1/27-tol <= value <= envelope(r)+tol
        is_star = sorted(degree) == [1]*(n-1)+[n-1]
        assert (abs(value-envelope(n-1)) < tol) == is_star
        stars += is_star
    print(f"n={n}  connected={count}  maximizers={stars}  maximum={max_value:.12g}")


if __name__ == "__main__":
    for n in range(2, 7):
        check(n)
