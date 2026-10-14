#!/usr/bin/env python3
"""Exact supporting checks for the written IV-01 proof, using stdlib only.

Finite fixtures do not prove the all-n theorem. The outside-row identities
are additionally checked as formal integer polynomials. No assert statements
are used; normal and python -O execution have identical validation behavior.
"""

import argparse
from fractions import Fraction
from functools import lru_cache
from itertools import combinations, permutations, product
import json
from pathlib import Path


def fail(message):
    raise SystemExit("FAIL: " + message)


def require(condition, message):
    if not condition:
        fail(message)


@lru_cache(maxsize=None)
def signed_permutations(n):
    return tuple(
        (p, (-1) ** sum(p[i] > p[j] for i in range(n) for j in range(i + 1, n)))
        for p in permutations(range(n))
    )


def determinant(matrix):
    """Independent Leibniz expansion; the empty determinant is one."""
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "nonsquare determinant input")
    value = 0
    for perm, sign in signed_permutations(n):
        term = sign
        for i, j in enumerate(perm):
            term *= matrix[i][j]
        value += term
    return value


def subdet(matrix, rows, columns):
    return determinant([[matrix[i][j] for j in columns] for i in rows])


def verify_nsr(matrix, signature, expected_zeros=None):
    n = len(matrix)
    require(n > 0 and all(len(row) == n for row in matrix), "invalid NSR dimensions")
    require(len(signature) == n and all(s in (-1, 1) for s in signature), "invalid signature")
    count = 0
    zeros = []
    for k in range(1, n + 1):
        for rows in combinations(range(n), k):
            for columns in combinations(range(n), k):
                value = subdet(matrix, rows, columns)
                count += 1
                require(signature[k - 1] * value >= 0,
                        "wrong minor sign: order=%d rows=%s columns=%s" % (k, rows, columns))
                if value == 0:
                    zeros.append([k, list(rows), list(columns)])
                    require(k != n, "singular endpoint")
    if expected_zeros is not None:
        require(zeros == expected_zeros, "zero-minor fixture differs")
    return count, zeros


def verify_endpoint_pair(a, b, signature):
    ca, _ = verify_nsr(a, signature)
    cb, _ = verify_nsr(b, signature)
    n = len(a)
    require(len(b) == n, "endpoint dimension mismatch")
    for i in range(n):
        for j in range(n):
            require(((-1) ** (i + j)) * (b[i][j] - a[i][j]) >= 0,
                    "endpoints are not in the claimed checker order")
    return ca + cb


def fekete_values(matrix, rows, subrows, columns, missing, cache=None):
    require(len(rows) == len(columns) and len(subrows) == len(rows) - 1,
            "invalid Fekete row dimensions")
    require(set(subrows) <= set(rows), "Fekete rows not nested")
    require(columns[0] < missing < columns[-1] and missing not in columns,
            "Fekete inserted column is not a missing interior column")

    def minor(rr, cc):
        key = (tuple(rr), tuple(cc))
        if cache is not None and key in cache:
            return cache[key]
        value = subdet(matrix, rr, cc)
        if cache is not None:
            cache[key] = value
        return value

    a, c = columns[0], columns[-1]
    inside = columns[1:-1]
    middle = tuple(sorted(inside + (missing,)))
    left = tuple(sorted(columns[1:] + (missing,)))
    right = tuple(sorted(columns[:-1] + (missing,)))
    lhs = minor(rows, columns) * minor(subrows, middle)
    term1 = minor(rows, left) * minor(subrows, tuple(sorted(inside + (a,))))
    term2 = minor(rows, right) * minor(subrows, tuple(sorted(inside + (c,))))
    return lhs, term1, term2


def check_fekete():
    # Three independent types: dense mixed signs, generalized Vandermonde,
    # and a sparse integer fixture with many exact zeros.
    matrices = [
        [[((17 * i + 11 * j + 7 * i * j + 3 * j * j) % 19) - 9
          for j in range(8)] for i in range(6)],
        [[(i + 1) ** j for j in range(8)] for i in range(6)],
        [[int(i == j) + (i + 1 if j == i + 2 else 0)
          - (j + 1 if i == j + 1 else 0) for j in range(8)] for i in range(6)],
    ]
    count = 0
    for matrix in matrices:
        cache = {}
        for k in range(2, 7):
            for rows in combinations(range(6), k):
                for subrows in combinations(rows, k - 1):
                    for columns in combinations(range(8), k):
                        for missing in range(columns[0] + 1, columns[-1]):
                            if missing in columns:
                                continue
                            lhs, one, two = fekete_values(
                                matrix, rows, subrows, columns, missing, cache)
                            require(lhs == one + two, "Fekete determinant identity")
                            count += 1
    return count


# Sparse integer polynomials in six commuting indeterminates. Monomials are
# tuples of variable indices; the empty tuple is the constant monomial.
def padd(a, b):
    result = dict(a)
    for monomial, coefficient in b.items():
        result[monomial] = result.get(monomial, 0) + coefficient
        if result[monomial] == 0:
            del result[monomial]
    return result


def pscale(a, scalar):
    return {m: c * scalar for m, c in a.items() if c * scalar != 0}


def pmul(a, b):
    result = {}
    for ma, ca in a.items():
        for mb, cb in b.items():
            monomial = tuple(sorted(ma + mb))
            result[monomial] = result.get(monomial, 0) + ca * cb
    return {m: c for m, c in result.items() if c != 0}


def pdet(matrix):
    result = {}
    for perm, sign in signed_permutations(len(matrix)):
        term = {(): sign}
        for i, j in enumerate(perm):
            term = pmul(term, matrix[i][j])
        result = padd(result, term)
    return result


def corner_matrices(rho, u, v, ht, hk, hl, one):
    # Columns outside the anchor can be left or right, and the strict
    # external row can be earlier or later. All four determinants agree.
    return (
        [[ht, hk, hl], [u, one, rho], [v, one, rho]],
        [[hk, hl, ht], [one, rho, u], [one, rho, v]],
        [[u, one, rho], [v, one, rho], [ht, hk, hl]],
        [[one, rho, u], [one, rho, v], [hk, hl, ht]],
    )


def symbolic_corner_data():
    rho, u, v, ht, hk, hl = ({(j,): 1} for j in range(6))
    d = padd(v, pscale(u, -1))
    q = padd(hl, pscale(pmul(rho, hk), -1))
    expected = pscale(pmul(d, q), -1)
    matrices = corner_matrices(rho, u, v, ht, hk, hl, {(): 1})
    return matrices, expected


def check_corners():
    matrices, expected = symbolic_corner_data()
    for matrix in matrices:
        require(pdet(matrix) == expected, "formal outside-row corner identity")
    count = len(matrices)
    for rho, u, v, ht, hk, hl in product((0, 1, 2), repeat=6):
        target = -(v - u) * (hl - rho * hk)
        for matrix in corner_matrices(rho, u, v, ht, hk, hl, 1):
            require(determinant(matrix) == target, "corner identity with zero coordinates")
            count += 1
    return count


def cauchy_five_pair():
    x = (Fraction(1), Fraction(2), Fraction(9, 4), Fraction(5, 2), Fraction(3))
    a = [[1 / (xx + yy) - Fraction(1, 6) for yy in x] for xx in reversed(x)]
    b = [row[:] for row in a]
    b[0][0] += Fraction(23, 840840)
    return a, b, (1, 1, 1, -1, -1)


def check_fixtures():
    minor_count = 0
    pair_count = 0
    three = [[Fraction(1), Fraction(1), Fraction(0)],
             [Fraction(1), Fraction(3, 2), Fraction(1)],
             [Fraction(0), Fraction(1), Fraction(1)]]
    count, zeros = verify_nsr(three, (1, 1, -1))
    minor_count += count
    require([z for z in zeros if z[0] == 1] == [[1, [0], [2]], [1, [2], [0]]],
            "three-by-three two-corner-zero fixture")

    a, b, signature = cauchy_five_pair()
    minor_count += verify_endpoint_pair(a, b, signature)
    pair_count += 1
    for t in (Fraction(1, 4), Fraction(1, 2), Fraction(3, 4)):
        middle = [[(1 - t) * a[i][j] + t * b[i][j] for j in range(5)] for i in range(5)]
        count, _ = verify_nsr(middle, signature)
        minor_count += count
    _, zeros = verify_nsr(a, signature)
    require(zeros == [[1, [0], [4]], [2, [3, 4], [0, 1]]],
            "Cauchy mixed-boundary zero list")

    fixture_path = Path(__file__).resolve().parent / "fixtures" / "cauchy6_boundary.json"
    data = json.loads(fixture_path.read_text(encoding="utf-8"))
    matrix = [[Fraction(value) for value in row] for row in data["matrix"]]
    require(data["signature"] == [1, 1, 1, -1, -1, -1], "n6 signature fixture changed")
    count, zeros = verify_nsr(matrix, data["signature"], data["zero_minors"])
    minor_count += count
    require(any(z[0] == 3 for z in zeros) and any(z[0] == 4 for z in zeros),
            "n6 fixture lost its two middle-order degeneracies")

    # Two independent free coordinates, rather than just a line segment.
    identity = [[Fraction(int(i == j)) for j in range(4)] for i in range(4)]
    low = [row[:] for row in identity]
    low[0][1] = low[2][3] = Fraction(1)
    minor_count += verify_endpoint_pair(low, identity, (1, 1, 1, 1))
    pair_count += 1
    for x, y in product((Fraction(0), Fraction(1, 2), Fraction(1)), repeat=2):
        middle = [row[:] for row in identity]
        middle[0][1], middle[2][3] = x, y
        count, _ = verify_nsr(middle, (1, 1, 1, 1))
        minor_count += count
    return minor_count, pair_count


NEGATIVE_CONTROLS = (
    "fekete-sign", "corner-sign", "wrong-signature", "singular-endpoint",
    "reversed-checker-order", "bad-endpoint-entry",
)


def negative_case(name):
    if name == "fekete-sign":
        matrix = [[(i + 1) ** j for j in range(5)] for i in range(3)]
        lhs, one, two = fekete_values(matrix, (0, 1, 2), (0, 1), (0, 2, 4), 1)
        require(two != 0, "negative-control fixture has a zero mutated term")
        require(lhs == one - two, "deliberately reversed Fekete term sign")
    elif name == "corner-sign":
        matrices, expected = symbolic_corner_data()
        require(pdet(matrices[0]) == pscale(expected, -1), "deliberately reversed corner sign")
    elif name == "wrong-signature":
        a, _, _ = cauchy_five_pair()
        verify_nsr(a, (1, 1, 1, 1, -1))
    elif name == "singular-endpoint":
        identity = [[Fraction(int(i == j)) for j in range(3)] for i in range(3)]
        singular = [row[:] for row in identity]
        singular[2][2] = Fraction(0)
        verify_endpoint_pair(singular, identity, (1, 1, 1))
    elif name == "reversed-checker-order":
        a, b, signature = cauchy_five_pair()
        verify_endpoint_pair(b, a, signature)
    elif name == "bad-endpoint-entry":
        a, b, signature = cauchy_five_pair()
        b[0][4] = Fraction(-1)
        verify_endpoint_pair(a, b, signature)
    else:
        fail("unknown negative control")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-control", choices=NEGATIVE_CONTROLS)
    args = parser.parse_args()
    if args.negative_control:
        # A corrupt input must trigger explicit SystemExit in a validator.
        # Returning zero would tell the external test that it was accepted.
        negative_case(args.negative_control)
        return

    fekete_count = check_fekete()
    corner_count = check_corners()
    minor_count, pair_count = check_fixtures()
    for name in NEGATIVE_CONTROLS:
        rejected = False
        try:
            negative_case(name)
        except SystemExit as exc:
            require(exc.code not in (None, 0), "negative control exited successfully: " + name)
            rejected = True
        require(rejected, "negative control accepted: " + name)
    print("PASS: %d Fekete identities; %d corner checks (4 formal polynomial identities); "
          "%d fixture minor checks; %d checker endpoint pairs; %d negative controls rejected."
          % (fekete_count, corner_count, minor_count, pair_count, len(NEGATIVE_CONTROLS)))
    print("Supporting exact checks only; the written proof supplies the all-n conclusion.")


if __name__ == "__main__":
    main()
