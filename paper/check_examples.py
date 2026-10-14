#!/usr/bin/env python3
"""Exact verification of the four examples in main.tex (standard library only).

Normal invocation prints a deterministic JSON summary.  --negative-control
alters one selected example and must fail.  No assertion is used for
validation, so optimization does not remove any check.
"""
import argparse
from fractions import Fraction as Q
from itertools import combinations, permutations, product
import json


def require(condition, message):
    if not condition:
        raise SystemExit("FAIL: " + message)


def determinant(matrix):
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "determinant shape")
    total = Q(0)
    for perm in permutations(range(n)):
        inversions = sum(perm[i] > perm[j] for i in range(n) for j in range(i + 1, n))
        term = Q((-1) ** inversions)
        for i in range(n):
            term *= matrix[i][perm[i]]
        total += term
    return total


def inverse(matrix):
    n = len(matrix)
    require(all(len(row) == n for row in matrix), "inverse shape")
    aug = [[Q(x) for x in matrix[i]] + [Q(i == j) for j in range(n)] for i in range(n)]
    for j in range(n):
        pivot = next((i for i in range(j, n) if aug[i][j]), None)
        require(pivot is not None, "singular inverse input")
        aug[j], aug[pivot] = aug[pivot], aug[j]
        divisor = aug[j][j]
        aug[j] = [x / divisor for x in aug[j]]
        for i in range(n):
            if i != j:
                multiplier = aug[i][j]
                aug[i] = [x - multiplier * y for x, y in zip(aug[i], aug[j])]
    result = [row[n:] for row in aug]
    require(all(sum(matrix[i][k] * result[k][j] for k in range(n)) == int(i == j)
                for i in range(n) for j in range(n)), "inverse identity")
    return result


def minor(matrix, rows, columns):
    return determinant([[matrix[i][j] for j in columns] for i in rows])


def sign_profile(matrix, signature, nonsingular=True):
    n = len(matrix)
    require(len(signature) == n and all(x in (-1, 1) for x in signature), "signature")
    counts = []
    zeros = []
    for k in range(1, n + 1):
        positive = zero = negative = 0
        for rows in combinations(range(n), k):
            for columns in combinations(range(n), k):
                d = minor(matrix, rows, columns)
                require(signature[k - 1] * d >= 0,
                        "wrong signed minor, order %d, rows %s, columns %s" % (k, rows, columns))
                positive += d > 0
                negative += d < 0
                zero += d == 0
                if not d:
                    zeros.append([k, [i + 1 for i in rows], [j + 1 for j in columns]])
        counts.append({"order": k, "positive": positive, "zero": zero, "negative": negative})
    if nonsingular:
        require(determinant(matrix) != 0, "singular endpoint")
    return {"counts": counts, "zeros": zeros}


def checker_order(a, b):
    return all((-1) ** (i + j) * (b[i][j] - a[i][j]) >= 0
               for i in range(len(a)) for j in range(len(a)))


def midpoint(a, b):
    return [[Q(a[i][j] + b[i][j], 2) for j in range(len(a))] for i in range(len(a))]


def direct_sum_identity(a, n):
    m = len(a)
    require(n >= m, "direct sum order")
    return [[Q(a[i][j]) if i < m and j < m else Q(int(i == j))
             for j in range(n)] for i in range(n)]


def check(negative_control):
    # Example 1: singular TN endpoints, and the exact five-dimensional lift.
    a = [[0, 0, 1], [0, 0, 0], [0, 0, 0]]
    b = [[1, 0, 1], [0, 0, 0], [1, 0, 1]]
    if negative_control == "singular":
        b[2][0] = 0
    for n in (3, 5):
        aa, bb = direct_sum_identity(a, n), direct_sum_identity(b, n)
        require(checker_order(aa, bb), "singular-example checker order")
        sign_profile(aa, (1,) * n, nonsingular=False)
        sign_profile(bb, (1,) * n, nonsingular=False)
        require(determinant(aa) == determinant(bb) == 0, "singular endpoints")
        require(minor(midpoint(aa, bb), (0, 2), (0, 2)) == Q(-1, 4), "singular-example bad minor")

    # Example 2: distinct signatures, despite invertible SSR endpoints.
    a, b = [[1, 2], [2, 1]], [[2, 1], [1, 2]]
    if negative_control == "signature":
        b[1][1] = 1
    require(checker_order(a, b), "different-signature checker order")
    require(not sign_profile(a, (1, -1))["zeros"], "first SSR endpoint")
    require(not sign_profile(b, (1, 1))["zeros"], "second SSR endpoint")
    require((determinant(a), determinant(b), determinant(midpoint(a, b))) == (-3, 3, 0),
            "different-signature determinants")

    # Example 3: ordinary lower and upper bounds do not suffice.
    for n in (2, 5):
        low = direct_sum_identity([[1, 2], [2, 5]], n)
        high = direct_sum_identity([[2, 3], [3, 6]], n)
        bad = direct_sum_identity([[1, 3], [3, 5]], n)
        if negative_control == "ordinary":
            bad[0][1] = Q(2)
        sign_profile(low, (1,) * n)
        sign_profile(high, (1,) * n)
        require(all(low[i][j] <= bad[i][j] <= high[i][j] for i in range(n) for j in range(n)),
                "ordinary interval membership")
        require((determinant(low), determinant(high)) == (1, 3), "ordinary endpoint determinants")
        require(minor(bad, (0, 1), (0, 1)) == -4, "ordinary-corner bad minor")

    # Example 4: a rational seed from the cited directed-fixed-entry manuscript.
    lam = (Q(1), Q(1, 10), Q(1, 100), Q(-1, 1000), Q(-1, 10000))
    seed = [[sum(lam[k] * Q(i * j, 36) ** k for k in range(5))
             for j in range(1, 6)] for i in range(1, 6)]
    seed[0][0] -= Q(500618646037, 19352067067828800)
    if negative_control == "degenerate":
        seed[0][0] += Q(1, 10**12)
    seed_profile = sign_profile(seed, (1, 1, 1, -1, 1))
    require(seed_profile["zeros"] == [[3, [1, 2, 3], [1, 2, 3]]], "seed zero-minor pattern")
    seed_inverse = inverse(seed)
    a = [[-(-1) ** (i + j) * seed_inverse[i][j] for j in range(5)] for i in range(5)]
    b = [row[:] for row in a]
    free = [(0, 0), (0, 1), (1, 0), (1, 1)]
    for i, j in free:
        b[i][j] += Q((-1) ** (i + j), 8)
    require(checker_order(a, b), "degenerate-box checker order")
    require([(i, j) for i in range(5) for j in range(5) if a[i][j] != b[i][j]] == free,
            "degenerate-box free coordinates")
    sig = (1, 1, -1, 1, -1)
    pa, pb = sign_profile(a, sig), sign_profile(b, sig)
    zero = [[2, [4, 5], [4, 5]]]
    require(pa["zeros"] == pb["zeros"] == zero, "endpoint zero-minor pattern")
    require(pa["counts"] == pb["counts"], "endpoint minor counts")
    require(all(a[i][j] > 0 and b[i][j] > 0 for i in range(5) for j in range(5)),
            "strictly positive endpoint entries")
    require(all(a[i][j] == b[i][j] for i in (3, 4) for j in (3, 4)), "fixed singular adjacent block")
    require(a[2][2] == b[2][2] and a[2][3] == b[2][3], "fixed positions of both parities")
    # R3 -> C2 -> R4 -> C3 -> R3, all fixed and nonzero.
    cycle = [("R", 3), ("C", 2), ("R", 4), ("C", 3), ("R", 3)]
    for left, right in zip(cycle, cycle[1:]):
        if left[0] == "R":
            i, j = left[1], right[1]
            require((i + j) % 2 == 1, "row-to-column edge parity")
        else:
            j, i = left[1], right[1]
            require((i + j) % 2 == 0, "column-to-row edge parity")
        require(a[i - 1][j - 1] == b[i - 1][j - 1] != 0, "directed-cycle fixed edge")
    periods = ((1, 1, 1, 1), (-1, -1, -1, -1), (1, -1, 1, -1), (-1, 1, -1, 1),
               (1, 1, -1, -1), (-1, -1, 1, 1), (1, -1, -1, 1), (-1, 1, 1, -1))
    old = set()
    for period in periods:
        v = tuple(period[i % 4] for i in range(5))
        old.add(v)
        old.add(v[:-1] + (-v[-1],))
    require(sig not in old, "signature outside the earlier list")
    # An independent finite check of this example's whole box: every minor is
    # multiaffine, and all sixteen ordinary vertices have the prescribed signs.
    for bits in product((0, 1), repeat=4):
        vertex = [row[:] for row in a]
        for (i, j), bit in zip(free, bits):
            if bit:
                vertex[i][j] = b[i][j]
        pv = sign_profile(vertex, sig)
        require(pv["zeros"] == zero, "ordinary-vertex zero pattern")
    return {
        "status": "PASS",
        "singular_endpoints": {"orders_checked": [3, 5], "bad_midpoint_minor": "-1/4"},
        "common_signature": {"endpoint_determinants": ["-3", "3"], "midpoint_determinant": "0"},
        "ordinary_vertices": {"orders_checked": [2, 5], "endpoint_determinants": ["1", "3"], "bad_minor": "-4"},
        "degenerate_box": {"dimension": 5, "free_entries": 4, "width": "1/8", "signature": list(sig),
                           "minor_counts_at_each_checker_vertex": pa["counts"], "zero_minors": zero,
                           "ordinary_vertices_checked": 16, "directed_cycle": [x[0] + str(x[1]) for x in cycle]},
    }


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--negative-control", nargs="?", const="degenerate",
                        choices=("singular", "signature", "ordinary", "degenerate"))
    args = parser.parse_args()
    print(json.dumps(check(args.negative_control), indent=2, sort_keys=True))
