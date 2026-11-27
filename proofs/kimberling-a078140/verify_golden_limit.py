"""Certify 24 decimal digits of the golden-slope positive ratio limit.

Only integer arithmetic is used.  At x=den/num the bounded first-difference
denominator has remainder at most 2*x**(N+1)/(1-x).  Its sign on either
side of the unique positive zero below (sqrt(5)-1)/2 gives the enclosure.
"""
from math import isqrt


def floor_n_phi(n):
    return (n + isqrt(5 * n * n)) // 2


def denominator_sign(recip_num, recip_den, cutoff=160):
    """Return the certified sign of D(recip_den / recip_num)."""
    coeffs = [
        (-1) ** j * (floor_n_phi(j + 1) - floor_n_phi(j))
        for j in range(cutoff + 1)
    ]
    # Scale D's truncation by recip_num**cutoff, then bound the tail
    # in the same units by 2*recip_den**(cutoff+1)/(recip_num-recip_den).
    scaled = sum(c * recip_den**j * recip_num**(cutoff-j)
                 for j, c in enumerate(coeffs))
    difference = recip_num - recip_den
    radius = 2 * recip_den**(cutoff+1)
    assert difference > 0 and abs(scaled) * difference > radius
    return 1 if scaled > 0 else -1


def main():
    digits = "688924110769165206686359"
    scale = 10**len(digits)
    lo = scale + int(digits)
    hi = lo + 1
    assert denominator_sign(lo, scale) == -1
    assert denominator_sign(hi, scale) == 1
    print(f"{lo}/{scale} < L(phi) < {hi}/{scale}")


if __name__ == "__main__":
    main()
