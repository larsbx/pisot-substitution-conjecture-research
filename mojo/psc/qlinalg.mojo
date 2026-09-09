"""Exact linear algebra over Q: RREF, rank, nullspace, span membership.

Used to *derive* — never to transcribe — the shuffle-kernel sector W_3 and to
decide the membership statements of the Spectral module certificate.
"""

from psc.rational import Rat, rat_zero, rat_one, rat_vec


def rref(m: List[List[Rat]]) -> Tuple[List[List[Rat]], List[Int]]:
    """Reduced row echelon form. Returns `(R, pivot_columns)`."""
    var r = List[List[Rat]]()
    for i in range(len(m)):
        r.append(m[i].copy())
    var pivots = List[Int]()
    if len(r) == 0:
        return (r^, pivots^)
    var ncols = len(r[0])
    var row = 0
    for c in range(ncols):
        if row == len(r):
            break
        var p = -1
        for i in range(row, len(r)):
            if not r[i][c].is_zero():
                p = i
                break
        if p < 0:
            continue
        r.swap_elements(row, p)
        var inv = r[row][c]
        for j in range(ncols):
            r[row][j] = r[row][j] / inv
        for i in range(len(r)):
            if i != row and not r[i][c].is_zero():
                var f = r[i][c]
                for j in range(ncols):
                    r[i][j] = r[i][j] - f * r[row][j]
        pivots.append(c)
        row += 1
    return (r^, pivots^)


def rank(m: List[List[Rat]]) -> Int:
    var res = rref(m)
    return len(res[1])


def nullspace(m: List[List[Rat]], ncols: Int) -> List[List[Rat]]:
    """Basis of `{x in Q^ncols : m . x = 0}`, one vector per free column."""
    var res = rref(m)
    ref r = res[0]
    ref pivots = res[1]
    var is_pivot = List[Bool]()
    for _ in range(ncols):
        is_pivot.append(False)
    for i in range(len(pivots)):
        is_pivot[pivots[i]] = True

    var basis = List[List[Rat]]()
    for f in range(ncols):
        if is_pivot[f]:
            continue
        var v = List[Rat]()
        for _ in range(ncols):
            v.append(rat_zero())
        v[f] = rat_one()
        for i in range(len(pivots)):
            v[pivots[i]] = -r[i][f]
        basis.append(v^)
    return basis^


def in_span(basis: List[List[Rat]], v: List[Rat]) -> Bool:
    """Whether `v` lies in the Q-span of `basis` (row vectors of equal length)."""
    var withv = List[List[Rat]]()
    for i in range(len(basis)):
        withv.append(basis[i].copy())
    var base_rank = rank(withv)
    withv.append(v.copy())
    return rank(withv) == base_rank


def matvec(m: List[List[Rat]], v: List[Rat]) -> List[Rat]:
    var out = List[Rat]()
    for i in range(len(m)):
        var s = rat_zero()
        for j in range(len(v)):
            s = s + m[i][j] * v[j]
        out.append(s)
    return out^


def is_zero_vec(v: List[Rat]) -> Bool:
    for i in range(len(v)):
        if not v[i].is_zero():
            return False
    return True
