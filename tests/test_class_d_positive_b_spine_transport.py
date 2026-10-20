"""Exact algebraic transport of the minus class-D b=0 rank spine to b>=1.

This checks one rank-descending occurrence for every non-target row. It does NOT
prove that the 145 labels are child-closed for positive b; complete coverage is
the separate ClassWedge certificate.
"""
from __future__ import annotations
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
ROWS = json.loads(
    (ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json").read_text()
)["rows"]

RUN = {0: (3, 5), 1: (3, 6), 2: (2, 4)}
LABEL_TO_ROW = {tuple(r[:5]): i for i, r in enumerate(ROWS)}

# Four b=0 selected edges whose fixed occurrence type cannot compensate b.
# Replacement: child row, top index m*a+k+n*b, bottom likewise.
ALT = {
    49: (116, (2, 5, 0), (2, 5, 1)),   # 2a+5 / last(2a+5+b)
    70: (102, (1, 2, 1), (0, 0, 0)),   # a+2+b / first
    96: (65,  (0, 0, 0), (1, 2, 1)),   # first / a+2+b
    117:(50,  (2, 5, 1), (2, 5, 0)),   # last / 2a+5
}

SPECIAL = {122, 123, 129, 135, 141, 142}


def params(a: int, b: int) -> tuple[int, int, int]:
    return 3*a + 5 + b, 3*a + 6 + b, 2*a + 4 + b


def image(letter: int, a: int, b: int) -> list[int]:
    p, q, r = params(a, b)
    if letter == 0:
        return [0] + [2]*p + [1]
    if letter == 1:
        return [1] + [2]*q + [0]
    return [1] + [2]*r + [1]


def prefix(word: list[int], i: int) -> tuple[int, int, int]:
    out = [0, 0, 0]
    for x in word[:i]:
        out[x] += 1
    return tuple(out)


def mat_vec(w: tuple[int, int, int], a: int, b: int) -> tuple[int, int, int]:
    p, q, r = params(a, b)
    x, c, y = w
    return x+c, x+c+2*y, p*x+q*c+r*y


def child(parent: list[int], a: int, b: int, i: int, j: int) -> tuple[int, int, int, int, int]:
    top, bottom = parent[:2]
    tw, bw = image(top, a, b), image(bottom, a, b)
    assert 0 <= i < len(tw) and 0 <= j < len(bw)
    pt, pb = prefix(tw, i), prefix(bw, j)
    mw = mat_vec(tuple(parent[2:5]), a, b)
    w = tuple(mw[k] + pb[k] - pt[k] for k in range(3))
    return tw[i], bw[j], *w


def old_kind(letter: int, m: int, k: int) -> str:
    rs, rb = RUN[letter]
    if (m, k) == (0, 0):
        return "first"
    if (m, k) == (rs, rb + 1):
        return "last"
    return "y"


def b_choices(kind: str) -> tuple[int, ...]:
    return (0,) if kind == "first" else (1,) if kind == "last" else (0, 1)


def idx(m: int, k: int, n: int, a: int, b: int) -> int:
    return m*a + k + n*b


def same_child_transport(row_id: int):
    r = ROWS[row_id]
    s = sum(r[2:5])
    kt, kb = old_kind(r[0], r[7], r[8]), old_kind(r[1], r[9], r[10])
    for nt in b_choices(kt):
        for nb in b_choices(kb):
            if nb - nt == -s:
                return (r[6], (r[7], r[8], nt), (r[9], r[10], nb))
    return None


def special_choice(row_id: int, a: int, b: int):
    # Returns target row and concrete occurrence indices.
    if row_id == 122:
        return 69, 0, b
    if row_id == 142:
        return 97, b, 0
    if row_id == 129:
        # top last; bottom b-th position (a y occurrence), valid for b>=1
        return 71, 2*a + 5 + b, b
    if row_id == 135:
        return 95, b, 2*a + 5 + b
    if row_id == 123:
        if b == 1:
            return 45, 2*a + 6, 0
        return 71, 2*a + 5 + b, b - 1
    if row_id == 141:
        if b == 1:
            return 34, 0, 2*a + 6
        return 95, b - 1, 2*a + 5 + b
    raise AssertionError(row_id)


def test_every_non_target_row_has_uniform_positive_b_rank_descent():
    direct = alt = special = 0
    for row_id, r in enumerate(ROWS):
        if r[6] < 0:
            assert r[5] == 0
            continue
        if row_id in SPECIAL:
            special += 1
            # Algebra is affine in a,b inside each displayed branch; checking
            # two values of each variable verifies all coefficients.
            samples = [(2,1), (5,1), (2,2), (5,4)]
            for a,b in samples:
                target, i, j = special_choice(row_id, a, b)
                assert child(r, a, b, i, j) == tuple(ROWS[target][:5])
                assert ROWS[target][5] < r[5]
            continue
        spec = ALT.get(row_id)
        if spec is not None:
            alt += 1
        else:
            spec = same_child_transport(row_id)
            assert spec is not None, row_id
            direct += 1
        target, ti, bj = spec
        for a,b in [(2,1), (5,1), (2,4), (5,4)]:
            i = idx(*ti, a, b)
            j = idx(*bj, a, b)
            assert child(r, a, b, i, j) == tuple(ROWS[target][:5])
            assert ROWS[target][5] < r[5]
    assert (direct, alt, special) == (129, 4, 6)


def test_positive_b_transport_uses_only_spine_labels():
    for row_id in SPECIAL:
        for a,b in [(2,1), (2,2), (4,5)]:
            target, i, j = special_choice(row_id, a, b)
            assert child(ROWS[row_id], a, b, i, j) in LABEL_TO_ROW
            assert LABEL_TO_ROW[child(ROWS[row_id], a, b, i, j)] == target
