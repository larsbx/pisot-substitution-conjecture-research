"""Independent Python oracle for kernel/psc/rauzy_torus.mojo.

Not theorem support. It recomputes, in a separately written language and by a
different route, every field of a `psc-rauzy-torus/v1` record:

* the scaled letter-frequency floors `F_i = floor(2^40 f_i)`, from a rational
  bisection bracket of the Perron root and a right eigenvector read off a
  cross product of two rows of `M - beta I` (the Mojo kernel instead decides
  each bit by a Sturm--Tarski sign query in Q(beta)); a floor is accepted only
  when both bracket endpoints agree, else the bracket is refined;
* the fixed-point prefix, the discrepancy enclosures, the floored plotting
  coordinates, the lift profile and the discrepancy bound.

Exact throughout (int and fractions.Fraction only).

Replay from the repository root:
    python3 oracles/python/rauzy_torus.py --check evidence/rauzy-torus-2026-10-21/named.jsonl
    python3 oracles/python/rauzy_torus.py --check evidence/rauzy-torus-2026-10-21/corpus.jsonl
"""

from __future__ import annotations

import argparse
import json
import sys
from fractions import Fraction

SCALE_BITS = 40
SCALE = 1 << SCALE_BITS
LIFT_SPAN = 256


def incidence(sigma: list[list[int]]) -> list[list[int]]:
    return [[img.count(i) for img in sigma] for i in range(3)]


def det3(m: list[list[int]]) -> int:
    return (
        m[0][0] * (m[1][1] * m[2][2] - m[1][2] * m[2][1])
        - m[0][1] * (m[1][0] * m[2][2] - m[1][2] * m[2][0])
        + m[0][2] * (m[1][0] * m[2][1] - m[1][1] * m[2][0])
    )


def charpoly(m: list[list[int]]) -> list[int]:
    """`[c0, c1, c2]` of `x^3 + c2 x^2 + c1 x + c0 = det(x I - M)`."""
    tr = m[0][0] + m[1][1] + m[2][2]
    minors = sum(m[i][i] * m[j][j] - m[i][j] * m[j][i] for i in range(3) for j in range(i + 1, 3))
    return [-det3(m), minors, -tr]


def _eval(c: list[int], x: Fraction) -> Fraction:
    return ((x + c[2]) * x + c[1]) * x + c[0]


def perron_bracket(m: list[list[int]], bits: int) -> tuple[Fraction, Fraction]:
    c = charpoly(m)
    lo, hi = Fraction(1), Fraction(1 + max(abs(x) for x in c))
    if _eval(c, lo) >= 0 or _eval(c, hi) <= 0:
        raise ValueError("Perron root not bracketed in (1, B]")
    for _ in range(bits):
        mid = (lo + hi) / 2
        lo, hi = (mid, hi) if _eval(c, mid) < 0 else (lo, mid)
    return lo, hi


def right_eigenvector(m: list[list[int]], beta: Fraction) -> list[Fraction]:
    """A nonzero cross product of two rows of `M - beta I` (kernel of it at beta)."""
    rows = [[Fraction(m[i][j]) - (beta if i == j else 0) for j in range(3)] for i in range(3)]
    for r in range(3):
        for s in range(r + 1, 3):
            a, b = rows[r], rows[s]
            v = [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]
            if any(v):
                return v
    raise ValueError("no nonzero cross product")


def frequency_floors(m: list[list[int]]) -> list[int]:
    for bits in (160, 320, 640):
        lo, hi = perron_bracket(m, bits)
        ends = []
        for beta in (lo, hi):
            v = right_eigenvector(m, beta)
            t = sum(v)
            ends.append([(SCALE * x / t).__floor__() for x in v])
        if ends[0] == ends[1]:
            return ends[0]
    raise ValueError("frequency floors not separated by the bracket")


def fixed_point_prefix(sigma: list[list[int]], length: int) -> list[int]:
    for k in range(1, 4):
        for a in range(3):
            b = a
            for _ in range(k):
                b = sigma[b][0]
            if b == a:
                w = [a]
                while len(w) < length:
                    nxt = w
                    for _ in range(k):
                        nxt = [y for x in nxt for y in sigma[x]][:length]
                    if len(nxt) <= len(w):
                        raise ValueError("prefix stopped growing")
                    w = nxt
                return w[:length]
    raise ValueError("no periodic first letter")


def record(sigma: list[list[int]], points: int, grid: int, coord_bits: int | None) -> dict:
    m = incidence(sigma)
    if abs(det3(m)) != 1:
        return {"status": "refused"}
    floors = frequency_floors(m)
    word = fixed_point_prefix(sigma, points)
    cell = SCALE // grid
    half = LIFT_SPAN // 2
    p = [0, 0]
    seen: set[tuple[int, int, int]] = set()
    lifts = [0] * (grid * grid)
    xs, ys, undecided, bound = [], [], 0, 0
    for n, letter in enumerate(word):
        hi = [SCALE * p[i] - n * floors[i] for i in range(2)]
        lo = [h - n for h in hi]
        bound = max(bound, *(abs(x) for x in (*hi, *lo, lo[0] + lo[1], hi[0] + hi[1])))
        if coord_bits is not None:
            xs.append(hi[0] >> (SCALE_BITS - coord_bits))
            ys.append(hi[1] >> (SCALE_BITS - coord_bits))
        cells = [h // cell for h in hi]
        if any((lo[i] // cell) != cells[i] for i in range(2)):
            undecided += 1
        else:
            lx, ly = cells[0] // grid, cells[1] // grid
            if not (-half <= lx < half and -half <= ly < half):
                raise ValueError("lift outside window")
            torus = (cells[0] % grid) * grid + cells[1] % grid
            if (torus, lx, ly) not in seen:
                seen.add((torus, lx, ly))
                lifts[torus] += 1
        if letter < 2:
            p[letter] += 1
    hist: dict[int, int] = {}
    for c in lifts:
        if c:
            hist[c] = hist.get(c, 0) + 1
    out = {
        "status": "diagnostic",
        "freq_floor": floors,
        "points": points,
        "sup_bound": bound,
        "grid": grid,
        "undecided": undecided,
        "occupied": sum(1 for c in lifts if c),
        "lift_keys": sorted(hist),
        "lift_counts": [hist[k] for k in sorted(hist)],
    }
    if coord_bits is not None:
        out.update(x=xs, y=ys, letter=word, lifts=lifts)
    return out


def check(path: str) -> int:
    failures = 0
    for count, line in enumerate(open(path), 1):
        mojo = json.loads(line)
        sigma = [[int(c) for c in img] for img in mojo["sigma"]]
        points = mojo.get("points", 1)
        grid = mojo.get("grid", 1)
        ours = record(sigma, points, grid, mojo.get("coord_bits"))
        bad = [k for k, v in ours.items() if mojo.get(k) != v]
        if bad:
            failures += 1
            print(f"MISMATCH {mojo.get('name', mojo.get('index'))}: {bad}", file=sys.stderr)
    print(json.dumps({"checked": count, "mismatches": failures, "file": path}))
    return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", required=True, help="a psc-rauzy-torus/v1 JSONL file")
    return check(parser.parse_args().check)


if __name__ == "__main__":
    raise SystemExit(main())
