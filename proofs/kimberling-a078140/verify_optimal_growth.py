"""Exact uniform disk certificate for Kimberling's floor reciprocal.

Let G be the signed floor series and D=(1+x)^2 G. The code checks each
possible prefix d[0:16] for 3/2 <= r < 5/3. For j>15, |d[j]| <= 1:
consecutive increments in the unsigned floors both belong to {1,2}.

For each prefix we choose a rational polynomial Q and c>0 so that
E=D*Q=1-c*x+O(x^11). A positive Rouche margin bounds the sum of the absolute
values of all other terms on |x|=3/5 by c*(3/5). The D-at-radius margin
guarantees D itself has a real zero inside; hence that zero is simple and
unique throughout the closed disk. The initial finite list checks the
5/3-factor growth condition, which the same Rouche margin propagates.
"""
from fractions import Fraction as F


R = F(3, 5)
N = 15
K = 10


def main():
    start, stop = F(3, 2), F(5, 3)
    # Floor((j+1)*r) can change at p/(j+1) only. Floor values at each
    # breakpoint agree with those immediately on its right.
    cells = sorted({F(p, q) for q in range(1, N + 2)
                    for p in range(1, 2*q) if start <= F(p, q) < stop})
    assert len(cells) == 13
    for r in cells:
        floors = [int((j + 1) * r) for j in range(N+1)]
        d = [(-1)**j * (floors[j] - (2*floors[j-1] if j else 0)
                         + (floors[j-2] if j >= 2 else 0)) for j in range(N+1)]
        assert d[0] == 1 and all(abs(v) <= 1 for v in d)
        u = [1]
        for j in range(1, K+2):
            u.append(-sum(d[i]*u[j-i] for i in range(1, j+1)))
        c = F(u[K], u[K-1])
        q = [u[j] - c * (u[j-1] if j else 0) for j in range(K)]
        a = [u[j] + (2*u[j-1] if j else 0) + (u[j-2] if j >= 2 else 0)
             for j in range(len(u))]
        assert all(3*y >= 5*x for x, y in zip(a, a[1:]))
        assert [i for i, (x, y) in enumerate(zip(a, a[1:])) if 3*y == 5*x] == [1]
        e = [sum(q[i]*d[j-i] for i in range(min(j, K-1) + 1))
             for j in range(N+1)]
        assert e[:K+1] == [1, -c] + [0]*(K-1)
        tail_factor = R**(N+1)/(1-R)
        remainder = sum(abs(e[j])*R**j for j in range(2, N+1))
        remainder += sum(abs(x) for x in q)*tail_factor
        margin = c*R - 1 - remainder
        d_margin = -(sum(v*R**j for j, v in enumerate(d)) + tail_factor)
        assert margin > 0 and d_margin > 0
        print(f"left endpoint {r}: Rouche margin {margin}, D margin {d_margin}")


if __name__ == "__main__":
    main()
