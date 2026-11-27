"""Compute A353890(29) exactly from prime-field collisions.

Usage: python verify_harkness.py
Only Python's standard library is required. No factor or residue tables
are inputs. The fixed expected values at the end are regression checks.
"""

from math import prod


def multiplication_matrix(n, exponent):
    """Multiply by 2-X-X^exponent modulo Φ_n=1+X+...+X^(n-1).

    n must be prime. Matrix columns correspond to 1,X,...,X^(n-2).
    Reduction first uses X^n=1, then X^(n-1)=-(1+...+X^(n-2)).
    """
    degree = n - 1
    matrix = [[0] * degree for _ in range(degree)]
    for col in range(degree):
        for power, coefficient in ((0, 2), (1, -1), (exponent, -1)):
            row = (col + power) % n
            if row < degree:
                matrix[row][col] += coefficient
            else:
                for row in range(degree):
                    matrix[row][col] -= coefficient
    return matrix


def determinant(matrix):
    """Fraction-free elimination, asserting exactness of every division."""
    size = len(matrix)
    previous = sign = 1
    for column in range(size - 1):
        pivot_row = next((r for r in range(column, size) if matrix[r][column]), None)
        if pivot_row is None:
            return 0
        if pivot_row != column:
            matrix[column], matrix[pivot_row] = matrix[pivot_row], matrix[column]
            sign = -sign
        pivot = matrix[column][column]
        for row in range(column + 1, size):
            for j in range(column + 1, size):
                num = pivot * matrix[row][j] - matrix[row][column] * matrix[column][j]
                value, remainder = divmod(num, previous)
                assert remainder == 0
                matrix[row][j] = value
        previous = pivot
    return sign * matrix[-1][-1]


def factor(n):
    """Return the prime factors with multiplicity by exhaustive trial division."""
    assert n > 0
    factors = []
    d = 2
    while d * d <= n:
        while n % d == 0:
            factors.append(d)
            n //= d
        d = 3 if d == 2 else d + 2
    if n > 1:
        factors.append(n)
    return factors


def collision(n, prime):
    """Produce a triple of consecutive residues with equal n-th powers."""
    # A collision supplies an element of order n in F_p^×.
    if (prime - 1) % n:
        return None
    for seed in range(2, prime):
        generator = pow(seed, (prime - 1) // n, prime)
        if generator != 1:
            break
    else:
        raise ArithmeticError("missing root of unity")
    for j in range(1, n):
        x = pow(generator, j, prime)
        if pow((2 - x) % prime, n, prime) == 1:
            m = (pow(1 - x, -1, prime) - 1) % prime
            residues = [pow(m + h, n, prime) for h in range(3)]
            assert residues[0] == residues[1] == residues[2]
            return m, residues[0]
    return None


def compute_period(n, verbose=False):
    """Compute the least positive period for a prime exponent n >= 5."""
    assert n >= 5 and factor(n) == [n]
    candidates = set()
    for exponent in range(2, n):
        norm = abs(determinant(multiplication_matrix(n, exponent)))
        factors = factor(norm)
        assert prod(factors) == norm
        candidates.update(factors)
        if verbose:
            print(f"t={exponent:2}  norm={norm:12}  factors={factors}")
    witnesses = {}
    for prime in sorted(candidates):
        witness = collision(n, prime)
        if witness is not None:
            witnesses[prime] = witness
    return prod(witnesses), witnesses


if __name__ == "__main__":
    for exponent, expected in (
        (5, 11), (7, 1247), (11, 1241058127), (13, 243641132605417),
        (17, 943422576750791493013356207217),
        (19, 607088607861933740557075591887834842297),
    ):
        assert compute_period(exponent)[0] == expected

    # Check every smaller prime in the domain of the conjecture. In each
    # case the predicted Jacobsthal number is itself the greatest factor.
    for exponent in (5, 7, 11, 13, 17, 19, 23):
        _, smaller_witnesses = compute_period(exponent)
        prediction = (2**exponent + 1) // 3
        assert max(smaller_witnesses) == prediction
        assert factor(2**exponent + 1) == [3, prediction]
        print(f"n={exponent}: greatest prime factor = {prediction}")

    period, witnesses = compute_period(29, verbose=True)
    print("\np : (m, common 29th-power residue)")
    for prime, witness in witnesses.items():
        print(f"{prime} : {witness}")
    print("\nleast period:", period)
    print("greatest prime factor:", max(witnesses))
    assert len(witnesses) == 17
    assert max(witnesses) == 108050869
    assert period == 23185169775494678703965601811862664516267203026525520380383050531459422153206071324389
    j = (2**29+1)//3
    assert factor(j) == [59,3033169]
    totient_prediction = prod(p-1 for p in factor(2**29+1))//2 + 1
    assert totient_prediction == 5 * 35184749
    print("Jacobsthal prediction:", j, "= 59 * 3033169")
    print("totient prediction:", totient_prediction, "= 5 * 35184749")
