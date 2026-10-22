"""Independent Python oracle for kernel/psc/rauzy_contacts.mojo.

Not theorem support. It recomputes the exact contact set of a
`psc-rauzy-contacts/v1` record by a different construction, in a separately
written language:

* the potential-overlap graph is `reference/psc_research/formal_overlap.py`'s
  `FormalGraph`, the inflation closure of a q-contraction region rather than
  Proposition V's box (both contain every cycle, so the descendants of cycles
  agree whenever both are right);
* the contacts are the non-coincidence descendants of its recurrent SCCs,
  with `t = <l, w>` solved for `w` over Q from this oracle's own left Perron
  vector;
* drawing coordinates and lattice neighbours are recomputed from the
  frequency floors of `oracles/python/rauzy_torus.py`.

Exact throughout (int and fractions.Fraction only).

Replay from the repository root:
    python3 oracles/python/rauzy_contacts.py --check evidence/rauzy-contacts-2026-10-22/contacts-named.jsonl
    python3 oracles/python/rauzy_contacts.py --check evidence/rauzy-contacts-2026-10-22/contacts-corpus.jsonl --limit 60
"""

from __future__ import annotations

import argparse
import json
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "reference"))

from psc_research.formal_overlap import FormalGraph  # noqa: E402
from psc_research.overlap_obstruction import sccs  # noqa: E402

TORUS = runpy.run_path(str(ROOT / "oracles/python/rauzy_torus.py"))
SCALE_BITS = TORUS["SCALE_BITS"]


def _solve(lengths, t) -> tuple[int, int, int]:
    """The integral `w` with `t = sum_a w_a l_a`, columns in the power basis."""
    a = [[Fraction(lengths[c][r]) for c in range(3)] + [Fraction(t[r])] for r in range(3)]
    for col in range(3):
        piv = next(r for r in range(col, 3) if a[r][col] != 0)
        a[col], a[piv] = a[piv], a[col]
        for r in range(3):
            if r != col and a[r][col] != 0:
                k = a[r][col] / a[col][col]
                a[r] = [x - k * y for x, y in zip(a[r], a[col])]
    w = [a[r][3] / a[r][r] for r in range(3)]
    if any(x.denominator != 1 for x in w):
        raise ValueError("offset is not an integral combination of tile lengths")
    return tuple(int(x) for x in w)


def _graph_contacts(g) -> set[tuple[int, int, int, int, int]]:
    recurrent = [c for c in sccs(g) if len(c) > 1 or any(v in g.adj[v] for v in c)]
    mark, stack = set(), [v for c in recurrent for v in c]
    while stack:
        v = stack.pop()
        if v in mark:
            continue
        mark.add(v)
        stack.extend(g.adj[v])
    out = set()
    for v in mark:
        top, bot, t = g.states[v]
        if g.is_coincidence(g.states[v]):
            continue
        out.add((top - 1, bot - 1, *_solve(g.l, t)))
    return out


def record(sigma: list[list[int]], coord_bits: int | None) -> dict:
    m = TORUS["incidence"](sigma)
    if abs(TORUS["det3"](m)) != 1:
        return {"status": "refused"}
    formal = FormalGraph({a + 1: [c + 1 for c in img] for a, img in enumerate(sigma)})
    if formal.capped:
        raise ValueError("formal graph capped")
    contacts = _graph_contacts(formal)
    if contacts != {(j, i, -a, -b, -c) for i, j, a, b, c in contacts}:
        raise ValueError("contacts not closed under reversal")
    lattice = {(a, b) for _, _, a, b, c in contacts if a + b + c == 0 and (a, b) != (0, 0)}
    out = {"status": "exact", "freq_floor": TORUS["frequency_floors"](m), "contacts": len(contacts),
           "lattice_contacts": sum(1 for *_, a, b, c in contacts if a + b + c == 0),
           "lattice_neighbours": lattice}
    if coord_bits is not None:
        f = out["freq_floor"]
        shift = SCALE_BITS - coord_bits
        rows = set()
        for i, j, a, b, c in contacts:
            s = a + b + c
            rows.add((i, j, a, b, c, ((a << SCALE_BITS) - s * f[0]) >> shift, ((b << SCALE_BITS) - s * f[1]) >> shift))
        out["contact_list"] = rows
    return out


def normalize(mojo: dict) -> dict:
    """The record's fields as the oracle compares them (lists of tuples as sets)."""
    out = dict(mojo)
    if "lattice_neighbours" in out:
        out["lattice_neighbours"] = {tuple(v) for v in out["lattice_neighbours"]}
    if "contact_list" in out:
        out["contact_list"] = {tuple(v) for v in out["contact_list"]}
    return out


def check(path: str, limit: int | None) -> int:
    failures = checked = 0
    for line in open(path):
        mojo = normalize(json.loads(line))
        if limit is not None and checked >= limit:
            break
        sigma = [[int(c) for c in img] for img in mojo["sigma"]]
        ours = record(sigma, mojo.get("coord_bits"))
        bad = [k for k, v in ours.items() if mojo.get(k) != v]
        checked += 1
        if bad:
            failures += 1
            print(f"MISMATCH {mojo.get('name', mojo.get('index'))}: {bad}", file=sys.stderr)
    print(json.dumps({"checked": checked, "mismatches": failures, "file": path}))
    return 1 if failures else 0


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", required=True, help="a psc-rauzy-contacts/v1 JSONL file")
    parser.add_argument("--limit", type=int, default=None, help="check only the first N records")
    args = parser.parse_args()
    return check(args.check, args.limit)


if __name__ == "__main__":
    raise SystemExit(main())
