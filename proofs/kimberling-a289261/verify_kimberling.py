"""Independently check OEIS A289261 from its defining reciprocal."""
from fractions import Fraction


def source_coefficients(count):
    """Invert the alternating floor series by triangular convolution."""
    r = Fraction(13, 8)
    kernel = [(-1)**n * ((n + 1) * r).__floor__() for n in range(count)]
    terms = [1]
    for n in range(1, count):
        terms.append(-sum(kernel[j] * terms[n-j] for j in range(1, n+1)))
    return terms


def check(count=1001):
    a = source_coefficients(count)
    assert a[:11] == [1, 3, 5, 9, 17, 30, 52, 91, 160, 281, 494]
    delta = [y - x for x, y in zip(a, a[1:])]
    assert all(d > 0 for d in delta)
    for k in range(3, count - 8):
        assert delta[k+7] == 2*a[k] + delta[k+2] + 2*delta[k+3] + 2*delta[k+4] + delta[k+5]
    print(f"Verified {count} defining coefficients and every applicable difference identity.")


if __name__ == "__main__":
    check()
