#!/usr/bin/env python3
"""Exact finite checks supporting, but not proving, the universal argument.

Only standard-library integers/Fractions. Determinants use the Leibniz
formula; inversion and rank use separate Fraction Gaussian elimination.
Every requirement fails closed with SystemExit, also under python -O.
"""
from fractions import Fraction as F
from itertools import combinations, permutations
import argparse


def require(condition, message):
    if not condition:
        raise SystemExit(message)


PERMS = {
    k: [(p, (-1) ** sum(p[i] > p[j] for i in range(k)
                       for j in range(i + 1, k)))
        for p in permutations(range(k))]
    for k in range(7)
}


def determinant(a):
    n = len(a)
    require(n <= 6 and all(len(row) == n for row in a), 'bad determinant size')
    total = F(0)
    for p, sign in PERMS[n]:
        value = F(sign)
        for i, j in enumerate(p):
            value *= a[i][j]
        total += value
    return total


def submatrix(a, rows, cols):
    return [[a[i][j] for j in cols] for i in rows]


def rank(a):
    if not a:
        return 0
    b = [[F(x) for x in row] for row in a]
    n = len(b[0])
    require(all(len(row) == n for row in b), 'ragged matrix')
    r = 0
    for j in range(n):
        h = next((i for i in range(r, len(b)) if b[i][j]), None)
        if h is None:
            continue
        b[r], b[h] = b[h], b[r]
        pivot = b[r][j]
        b[r] = [x / pivot for x in b[r]]
        for i in range(r + 1, len(b)):
            coeff = b[i][j]
            b[i] = [x - coeff * y for x, y in zip(b[i], b[r])]
        r += 1
        if r == len(b):
            break
    return r


def inverse(a):
    n = len(a)
    b = [[F(x) for x in row] + [F(i == j) for j in range(n)]
         for i, row in enumerate(a)]
    for j in range(n):
        h = next((i for i in range(j, n) if b[i][j]), None)
        require(h is not None, 'singular inversion pivot')
        b[j], b[h] = b[h], b[j]
        pivot = b[j][j]
        b[j] = [x / pivot for x in b[j]]
        for i in range(n):
            if i != j:
                coeff = b[i][j]
                b[i] = [x - coeff * y for x, y in zip(b[i], b[j])]
    return [row[n:] for row in b]


def signed_schur(a, krows, lcols, insert_signs=True):
    n = len(a)
    require(krows == sorted(krows) and lcols == sorted(lcols), 'unsorted pivot')
    require(len(krows) == len(lcols), 'nonsquare pivot')
    p = submatrix(a, krows, lcols)
    require(determinant(p) != 0, 'singular Schur pivot')
    pinv = inverse(p)
    rr = [i for i in range(n) if i not in krows]
    cc = [j for j in range(n) if j not in lcols]
    s = []
    for i in rr:
        row = []
        for j in cc:
            value = F(a[i][j]) - sum(
                F(a[i][lcols[u]]) * pinv[u][v] * a[krows[v]][j]
                for u in range(len(krows)) for v in range(len(krows)))
            if insert_signs:
                value *= (-1) ** (sum(k > i for k in krows) +
                                   sum(l > j for l in lcols))
            row.append(value)
        s.append(row)
    return s, rr, cc


def check_schur(a, krows, lcols, insert_signs=True):
    s, rr, cc = signed_schur(a, krows, lcols, insert_signs)
    pivot = determinant(submatrix(a, krows, lcols))
    count = 0
    for q in range(1, len(s) + 1):
        for ui in combinations(range(len(rr)), q):
            for vi in combinations(range(len(cc)), q):
                rows = sorted(krows + [rr[i] for i in ui])
                cols = sorted(lcols + [cc[j] for j in vi])
                lhs = determinant(submatrix(s, ui, vi))
                rhs = determinant(submatrix(a, rows, cols)) / pivot
                require(lhs == rhs, 'signed Schur minor identity failed')
                count += 1
    return count


def check_signature(a, eps):
    n = len(a)
    require(len(eps) == n and all(e in (-1, 1) for e in eps), 'bad signature')
    count = 0
    for q in range(1, n + 1):
        for rows in combinations(range(n), q):
            for cols in combinations(range(n), q):
                d = determinant(submatrix(a, rows, cols))
                require(eps[q - 1] * d >= 0, 'incorrect signed minor')
                count += 1
    require(determinant(a) != 0, 'singular sign-regular fixture')
    return count


def check_maximal_rectangle(a, eps, rr, cc, claimed_rank):
    require(rank(submatrix(a, rr, cc)) == claimed_rank, 'incorrect rank claim')
    require(len(rr) + len(cc) == len(a) + claimed_rank,
            'rectangle is not saturated')
    require(min(len(rr), len(cc)) > claimed_rank, 'degenerate rectangle')
    e = [1] + eps
    eta = [e[claimed_rank + q] * e[claimed_rank]
           for q in range(len(a) - claimed_rank + 1)]
    for q, value in enumerate(eta):
        require(value == eta[1] ** q * eta[2] ** (q * (q - 1) // 2),
                'periodic tail formula failed')


def extend_rank_and_check_zero(a, rr, cc, p):
    t = rank(submatrix(a, rr, cc))
    require(t <= p <= len(rr), 'bad rank-extension parameters')
    chosen = []
    for j in cc:
        if rank(submatrix(a, rr, chosen + [j])) > len(chosen):
            chosen.append(j)
    require(len(chosen) == t, 'basis selection failed')
    for j in range(len(a)):
        if len(chosen) == p:
            break
        if j not in chosen and rank(submatrix(a, rr, chosen + [j])) > len(chosen):
            require(j not in cc, 'extension unexpectedly uses dependent C column')
            chosen.append(j)
    require(len(chosen) == p, 'column basis did not extend')
    ll = sorted(chosen)
    kk = next((list(kk) for kk in combinations(rr, p)
               if determinant(submatrix(a, kk, ll)) != 0), None)
    require(kk is not None, 'pivot row selection failed')
    s, sr, sc = signed_schur(a, kk, ll)
    zero_rows = [i for i in rr if i not in kk]
    zero_cols = [j for j in cc if j not in ll]
    require(len(zero_rows) == len(rr) - p, 'wrong zero-row count')
    require(len(zero_cols) == len(cc) - t, 'wrong zero-column count')
    require(all(s[sr.index(i)][sc.index(j)] == 0
                for i in zero_rows for j in zero_cols),
            'rank-extension rectangle did not vanish')
    return len(zero_rows), len(zero_cols)


def rejected(call):
    try:
        call()
    except SystemExit:
        return True
    return False


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--negative-control', choices=[
        'missing_insertion_sign', 'wrong_rank', 'wrong_signature',
        'singular', 'all_ones'])
    args = parser.parse_args()
    moments = [100 * (1 + 2 ** m) for m in range(11)]
    for m, value in enumerate([1, 30, 300, 2000], 7):
        moments[m] += value
    hankel = [[moments[i + j] for j in range(6)] for i in range(6)]
    hinge = [[2 ** max(i + j - 4, 0) for j in range(5)] for i in range(5)]
    ident = [[int(i == j) for j in range(4)] for i in range(4)]
    reverse = [[int(i + j == 4) for j in range(5)] for i in range(5)]
    a = [[1, 0, 0, 0], [1, 1, 0, 0], [0, 1, 1, 0], [0, 0, 1, 1]]
    b = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 1, 1, 0], [0, 1, 1, 1]]
    fixtures = [
        (hankel, [1, 1, 1, -1, -1, 1]),
        (hinge, [1, 1, -1, -1, 1]),
        (ident, [1] * 4),
        (reverse, [1, -1, -1, 1, 1]),
        (a, [1] * 4), (b, [1] * 4),
    ]
    wrong_signature = fixtures[0][1][:]
    wrong_signature[3] *= -1
    singular = [row[:] for row in hankel]
    singular[-1] = singular[-2][:]
    controls = {
        'missing_insertion_sign': lambda: check_schur(hankel, [1], [2], insert_signs=False),
        'wrong_rank': lambda: check_maximal_rectangle(hankel, fixtures[0][1],
                              list(range(4)), list(range(4)), 1),
        'wrong_signature': lambda: check_signature(hankel, wrong_signature),
        'singular': lambda: check_signature(singular, fixtures[0][1]),
        'all_ones': lambda: check_signature([[1] * 6 for _ in range(6)], fixtures[0][1]),
    }
    if args.negative_control is not None:
        # Successful rejection exits nonzero inside the verifier. A returned
        # callback deliberately exits zero so the external runner sees failure.
        controls[args.negative_control]()
        print('NEGATIVE CONTROL WAS ACCEPTED:', args.negative_control)
        return
    sign_checks = sum(check_signature(m, e) for m, e in fixtures)
    schur_checks = 0
    for matrix, pivots in [
        (hankel, [([0], [0]), ([1], [2]), ([4], [1]),
                  ([0, 3], [1, 4]), ([1, 4], [0, 5]),
                  ([0, 2, 5], [1, 3, 4])]),
        (hinge, [([0], [2]), ([3], [0]), ([0, 3], [0, 3])]),
        (a, [([1], [0]), ([1, 3], [0, 3])]),
        (reverse, [([1], [3]), ([0, 3], [1, 4])]),
    ]:
        for rows, cols in pivots:
            schur_checks += check_schur(matrix, rows, cols)

    check_maximal_rectangle(hankel, fixtures[0][1], list(range(4)), list(range(4)), 2)
    check_maximal_rectangle(hinge, fixtures[1][1], list(range(3)), list(range(3)), 1)
    check_maximal_rectangle(ident, fixtures[2][1], [0, 2], [1, 3], 0)
    check_maximal_rectangle(reverse, fixtures[3][1], [0, 2], [0, 1, 3], 0)
    require(extend_rank_and_check_zero(hinge, [0, 1, 2], [0, 1, 2], 2) == (1, 2),
            'unexpected strict rank-extension fixture')
    require(extend_rank_and_check_zero(hankel, list(range(4)), list(range(4)), 2) == (2, 2),
            'unexpected Hankel zero rectangle')

    # Endpoint rank increase really occurs; universal proof must not assume otherwise.
    require(all((-1) ** (i + j) * (b[i][j] - a[i][j]) >= 0
                for i in range(4) for j in range(4)), 'endpoints are not checker ordered')
    middle = [[F(a[i][j] + b[i][j], 2) for j in range(4)] for i in range(4)]
    rr, cc = [1, 3], [0, 1]
    require(determinant(submatrix(a, rr, cc)) == 0 and
            determinant(submatrix(b, rr, cc)) == 0, 'endpoint minor is nonzero')
    require(determinant(submatrix(middle, rr, cc)) == F(1, 4), 'midpoint determinant failed')
    require(rank(submatrix(middle, rr, cc)) == 2, 'midpoint rank failed')

    # Negative controls exercise the three most consequential conventions.
    for name, call in controls.items():
        require(rejected(call), 'negative control was accepted: ' + name)
    print('PASS:', sign_checks, 'exact signed minors in six nonsingular fixtures.')
    print('PASS:', schur_checks, 'arbitrary-pivot signed Schur minor identities.')
    print('PASS: four saturated-rank fixtures and two basis-extension zero rectangles.')
    print('PASS: TN checker endpoints have zero minor but midpoint minor 1/4.')
    print('PASS: five negative controls reject insertion-sign, rank, signature, and singularity errors.')
    print('Finite checks support formulas and examples; they do not prove the universal theorem.')


if __name__ == '__main__':
    main()
