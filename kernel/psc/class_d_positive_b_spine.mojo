"""Exact two-parameter transport of the 145-row minus class-D rank spine.

For every non-target row this module proves, coefficient by coefficient, a
valid pair of child indices whose computed overlap state is a sealed label of
strictly lower rank for every integer a>=2,b>=1.  This is an algebraic
occurrence-state certificate: it does not by itself prove that the selected
child tiles overlap geometrically at every parameter. Positive-b carrier
closure and conditional child realness are separate #139 obligations.

Index triples are [a_coefficient, constant, b_coefficient].
"""
from psc.class_d_minus_spine_data import minus_spine_rows


def _run(letter: Int) -> List[Int]:
    # y-run = a_coeff*a + constant + b
    if letter == 0:
        return [3, 5, 1]
    if letter == 1:
        return [3, 6, 1]
    return [2, 4, 1]


def _start(letter: Int) -> Int:
    return 0 if letter == 0 else 1


def _end(letter: Int) -> Int:
    return 0 if letter == 1 else 1


def _affine_nonnegative(ca: Int, c0: Int, cb: Int, amin: Int, bmin: Int) -> Bool:
    # On the unbounded quadrant a>=amin,b>=bmin this is iff both slopes are
    # nonnegative and the value at the corner is nonnegative.
    return ca >= 0 and cb >= 0 and ca*amin + c0 + cb*bmin >= 0


def _occurrence(
    letter: Int, index: List[Int], amin: Int, bmin: Int
) raises -> List[List[Int]]:
    """Return child letter and the three affine prefix coordinates.

    Output rows: [child], then prefix-x, prefix-c, prefix-y; each prefix
    coordinate is [a_coeff, constant, b_coeff].
    """
    if len(index) != 3:
        raise Error("occurrence index must be affine triple")
    var ma = index[0]
    var k = index[1]
    var nb = index[2]
    var run = _run(letter)

    var out = List[List[Int]]()
    if ma == 0 and k == 0 and nb == 0:
        out.append([_start(letter)])
        out.append([0,0,0])
        out.append([0,0,0])
        out.append([0,0,0])
        return out^

    if ma == run[0] and k == run[1]+1 and nb == 1:
        out.append([_end(letter)])
        out.append([0, 1 if _start(letter) == 0 else 0, 0])
        out.append([0, 1 if _start(letter) == 1 else 0, 0])
        out.append([run[0], run[1], 1])
        return out^

    # Interior y occurrence: 1 <= index <= run.
    if not _affine_nonnegative(ma, k-1, nb, amin, bmin):
        raise Error("selected index is not uniformly after the first letter")
    if not _affine_nonnegative(
        run[0]-ma, run[1]-k, 1-nb, amin, bmin
    ):
        raise Error("selected index leaves the y-run")
    out.append([2])
    out.append([0, 1 if _start(letter) == 0 else 0, 0])
    out.append([0, 1 if _start(letter) == 1 else 0, 0])
    out.append([ma, k-1, nb])
    return out^


def _prefix_component(occ: List[List[Int]], coord: Int) -> List[Int]:
    return occ[1+coord].copy()


def _verify_edge(
    rows: List[List[Int]], source: Int, target: Int,
    top_index: List[Int], bottom_index: List[Int],
    amin: Int = 2, bmin: Int = 1,
) raises:
    if source < 0 or source >= len(rows) or target < 0 or target >= len(rows):
        raise Error("spine row index out of range")
    ref r = rows[source]
    ref t = rows[target]
    if t[5] >= r[5]:
        raise Error("positive-b edge does not strictly decrease rank")

    var top = _occurrence(r[0], top_index, amin, bmin)
    var bottom = _occurrence(r[1], bottom_index, amin, bmin)
    if top[0][0] != t[0] or bottom[0][0] != t[1]:
        raise Error("positive-b occurrence has wrong child letters")

    var x = r[2]
    var c = r[3]
    var y = r[4]

    # M(a,b)w. First two coordinates are constant. Third coordinate is
    # (3x+3c+2y)a + (5x+6c+4y) + (x+c+y)b.
    var mw = List[List[Int]]()
    mw.append([0, x+c, 0])
    mw.append([0, x+c+2*y, 0])
    mw.append([3*x+3*c+2*y, 5*x+6*c+4*y, x+c+y])

    for coord in range(3):
        var pt = _prefix_component(top, coord)
        var pb = _prefix_component(bottom, coord)
        var ca = mw[coord][0] + pb[0] - pt[0]
        var c0 = mw[coord][1] + pb[1] - pt[1]
        var cb = mw[coord][2] + pb[2] - pt[2]
        if ca != 0 or cb != 0 or c0 != t[2+coord]:
            raise Error("positive-b affine child offset mismatch")


def _kind_choices(letter: Int, m: Int, k: Int) raises -> List[Int]:
    """Allowed b coefficients preserving the b=0 occurrence type."""
    var run = _run(letter)
    if m == 0 and k == 0:
        return [0]  # first
    if m == run[0] and k == run[1]+1:
        return [1]  # last
    # Prove directly that m*a+k is an interior y occurrence for every a>=2
    # on b=0 before transporting it.  Then b coefficient 0 tracks the run
    # start and coefficient 1 tracks the run end.
    if not _affine_nonnegative(m, k-1, 0, 2, 0):
        raise Error("sealed occurrence is not uniformly after the first letter")
    if not _affine_nonnegative(run[0]-m, run[1]-k, 0, 2, 0):
        raise Error("sealed occurrence is not uniformly inside its y-run")
    return [0,1]


def _direct_transport(rows: List[List[Int]], source: Int) raises -> Bool:
    ref r = rows[source]
    if r[6] < 0:
        return False
    var top_choices = _kind_choices(r[0], r[7], r[8])
    var bottom_choices = _kind_choices(r[1], r[9], r[10])
    var sumw = r[2]+r[3]+r[4]
    for nt in top_choices:
        for nb in bottom_choices:
            if nb-nt != -sumw:
                continue
            _verify_edge(
                rows, source, r[6],
                [r[7],r[8],nt], [r[9],r[10],nb],
            )
            return True
    return False


def _verify_alt(rows: List[List[Int]], source: Int) raises -> Bool:
    if source == 49:
        _verify_edge(rows,49,116,[2,5,0],[2,5,1])
    elif source == 70:
        _verify_edge(rows,70,102,[1,2,1],[0,0,0])
    elif source == 96:
        _verify_edge(rows,96,65,[0,0,0],[1,2,1])
    elif source == 117:
        _verify_edge(rows,117,50,[2,5,1],[2,5,0])
    else:
        return False
    return True


def _verify_special(rows: List[List[Int]], source: Int) raises -> Bool:
    if source == 122:
        _verify_edge(rows,122,69,[0,0,0],[0,0,1])
    elif source == 142:
        _verify_edge(rows,142,97,[0,0,1],[0,0,0])
    elif source == 129:
        _verify_edge(rows,129,71,[2,5,1],[0,0,1])
    elif source == 135:
        _verify_edge(rows,135,95,[0,0,1],[2,5,1])
    elif source == 123:
        # b=1 line: top index 2a+6, bottom first.
        _verify_fixed_b(rows,123,45,[2,6,0],[0,0,0],1)
        # b>=2 quadrant.
        _verify_edge(rows,123,71,[2,5,1],[0,-1,1],2,2)
    elif source == 141:
        _verify_fixed_b(rows,141,34,[0,0,0],[2,6,0],1)
        _verify_edge(rows,141,95,[0,-1,1],[2,5,1],2,2)
    else:
        return False
    return True


def _verify_fixed_b(
    rows: List[List[Int]], source: Int, target: Int,
    top_index: List[Int], bottom_index: List[Int], bvalue: Int,
) raises:
    """Coefficient proof on the one-parameter line b=bvalue, a>=2."""
    if source < 0 or source >= len(rows) or target < 0 or target >= len(rows):
        raise Error("fixed-b spine row index out of range")
    ref r = rows[source]
    ref t = rows[target]
    if t[5] >= r[5]:
        raise Error("fixed-b edge does not strictly decrease rank")

    # Substitute b=bvalue into the occurrence index before validating it.
    var ti: List[Int] = [top_index[0], top_index[1]+top_index[2]*bvalue, 0]
    var bi: List[Int] = [bottom_index[0], bottom_index[1]+bottom_index[2]*bvalue, 0]
    var top = _occurrence_fixed_b(r[0], ti, bvalue)
    var bottom = _occurrence_fixed_b(r[1], bi, bvalue)
    if top[0][0] != t[0] or bottom[0][0] != t[1]:
        raise Error("fixed-b occurrence has wrong child letters")

    var x = r[2]
    var c = r[3]
    var y = r[4]
    var mw = List[List[Int]]()
    mw.append([0, x+c])
    mw.append([0, x+c+2*y])
    mw.append([3*x+3*c+2*y, 5*x+6*c+4*y + bvalue*(x+c+y)])

    for coord in range(3):
        ref pt = top[1+coord]
        ref pb = bottom[1+coord]
        var ca = mw[coord][0] + pb[0] - pt[0]
        var c0 = mw[coord][1] + pb[1] - pt[1]
        if ca != 0 or c0 != t[2+coord]:
            raise Error("fixed-b affine child offset mismatch")


def _occurrence_fixed_b(
    letter: Int, index: List[Int], bvalue: Int
) raises -> List[List[Int]]:
    """One-parameter analogue: coordinate rows are [a_coeff, constant]."""
    var ma = index[0]
    var k = index[1]
    var run = _run(letter)
    var run_const = run[1]+bvalue

    var out = List[List[Int]]()
    if ma == 0 and k == 0:
        out.append([_start(letter)])
        out.append([0,0])
        out.append([0,0])
        out.append([0,0])
        return out^
    if ma == run[0] and k == run_const+1:
        out.append([_end(letter)])
        out.append([0, 1 if _start(letter) == 0 else 0])
        out.append([0, 1 if _start(letter) == 1 else 0])
        out.append([run[0], run_const])
        return out^

    if ma < 0 or ma*2+k < 1:
        raise Error("fixed-b selected index is not uniformly positive")
    var ua = run[0]-ma
    var u0 = run_const-k
    if ua < 0 or ua*2+u0 < 0:
        raise Error("fixed-b selected index leaves y-run")
    out.append([2])
    out.append([0, 1 if _start(letter) == 0 else 0])
    out.append([0, 1 if _start(letter) == 1 else 0])
    out.append([ma, k-1])
    return out^


def positive_b_target_row(rows: List[List[Int]], source: Int, branch: Int = 2) raises -> Int:
    """Target row used by the certified positive-b descent.

    branch=1 means the exceptional b=1 line; branch=2 means the b>=2
    quadrant. For rows without a piecewise exceptional target, both branches
    return the same row.
    """
    if source < 0 or source >= len(rows):
        raise Error("positive-b target source out of range")
    if branch != 1 and branch != 2:
        raise Error("positive-b target branch must be 1 or 2")
    if rows[source][6] < 0:
        return -1
    if source == 49:
        return 116
    if source == 70:
        return 102
    if source == 96:
        return 65
    if source == 117:
        return 50
    if source == 122:
        return 69
    if source == 142:
        return 97
    if source == 129:
        return 71
    if source == 135:
        return 95
    if source == 123:
        return 45 if branch == 1 else 71
    if source == 141:
        return 34 if branch == 1 else 95
    return rows[source][6]

def verify_minus_positive_b_spine() raises -> List[Int]:
    var rows = minus_spine_rows()
    if len(rows) != 145:
        raise Error("sealed minus spine row count changed")
    var targets = 0
    var direct = 0
    var alt = 0
    var special = 0
    var maximum = 0
    for i in range(len(rows)):
        maximum = max(maximum, rows[i][5])
        if rows[i][6] < 0:
            if rows[i][5] != 0 or rows[i][2] != 0 or rows[i][3] != 0 or rows[i][4] != 0:
                raise Error("target row is not rank-zero offset-zero")
            targets += 1
            continue
        if _direct_transport(rows,i):
            direct += 1
            continue
        if _verify_alt(rows,i):
            alt += 1
            continue
        if _verify_special(rows,i):
            special += 1
            continue
        raise Error("positive-b spine row has no certified rank descent: " + String(i))
    if targets != 6 or direct != 129 or alt != 4 or special != 6 or maximum != 4:
        raise Error("positive-b spine partition or rank bound changed")
    return [len(rows),targets,direct,alt,special,maximum]
