"""Cross-check A289245 by direct integer series inversion."""

from math import isqrt


def golden_floor(k):
    # floor(k*(3+sqrt(5))/2) = floor((3*k+floor(sqrt(5*k^2)))/2).
    return (3*k + isqrt(5*k*k)) // 2


def coefficients(floor_at, length):
    kernel = [(-1)**n * (floor_at(n+1) - 1) for n in range(length)]
    assert kernel[0] == 1
    result = [1]
    for n in range(1, length):
        result.append(-sum(kernel[i] * result[n-i] for i in range(1, n+1)))
    return result


def main():
    expected = [
        1, 4, 10, 25, 64, 162, 408, 1027, 2584, 6500, 16351, 41132,
        103468, 260272, 654709, 1646907, 4142758, 10421013, 26213819,
        65940258, 165871197, 417245167, 1049570586, 2640170577,
        6641288127, 16706006942, 42023574736, 105709331958,
        265909383794, 668888915293,
    ]
    a = coefficients(golden_floor, 1001)
    assert a[:len(expected)] == expected
    assert all(v >= 2*u for u, v in zip(a, a[1:]))
    print("Matched all 30 OEIS terms and 1000 successive doubling bounds.")


if __name__ == "__main__":
    main()
