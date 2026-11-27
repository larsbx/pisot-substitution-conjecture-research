"""Independent exact replay of the diagonal residual certificates.

This oracle uses Python integers and Fraction enclosures of the positive
cubic root. It does not import the canonical Mojo implementation or its
Sturm--Tarski sign routine. A comparison that remains unresolved is refused.
The finite square and the strict disk are deliberately different domains.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
from collections import deque
from fractions import Fraction
from functools import lru_cache
from pathlib import Path

PARAMETERS = (12, 13, 15, 16, 18, 20, 32)


def root_interval(r: int, bits: int = 96) -> tuple[int, int, int]:
    if not 12 <= r <= 4096 or not 32 <= bits <= 768:
        raise ValueError("unsupported root parameter or precision budget")
    scale = 1 << bits
    lo, hi = r * scale, (r + 1) * scale

    def polynomial(n: int) -> int:
        return n**3 - r*n*n*scale - 2*n*scale**2 - r*scale**3

    if not polynomial(lo) < 0 < polynomial(hi):
        raise ValueError("root interval is not bracketed")
    # f' is positive on [r,r+1]: 3*x^2-2*r*x-2 >= r^2-2 > 0.
    while hi - lo > 1:
        mid = (lo + hi) // 2
        value = polynomial(mid)
        if value == 0:
            raise ValueError("unexpected rational root")
        if value < 0:
            lo = mid
        else:
            hi = mid
    return lo, hi, scale


def sign_function(r: int):
    intervals = {96: root_interval(r)}

    @lru_cache(maxsize=None)
    def sign(c: tuple[int, int, int]) -> int:
        if c == (0, 0, 0):
            return 0
        for bits in (96, 192, 384, 768):
            if bits not in intervals:
                intervals[bits] = root_interval(r, bits)
            lo, hi, scale = intervals[bits]
            lower = c[0]*scale**2 + c[1]*(lo if c[1] >= 0 else hi)*scale
            lower += c[2]*(lo if c[2] >= 0 else hi)**2
            upper = c[0]*scale**2 + c[1]*(hi if c[1] >= 0 else lo)*scale
            upper += c[2]*(hi if c[2] >= 0 else lo)**2
            if lower > 0:
                return 1
            if upper < 0:
                return -1
        raise ValueError(f"unresolved polynomial sign at r={r}: {c}")

    return sign, intervals[96]


def graph(r: int):
    sign, (lo, hi, scale) = sign_function(r)
    a = (Fraction(lo, scale)-r, Fraction(hi, scale)-r)
    b = (Fraction(r*scale, hi), Fraction(r*scale, lo))

    def digits(z: int, y: int, bound: int = r) -> list[int]:
        wl = a[0 if y >= 0 else 1]*y + b[0 if z >= 0 else 1]*z
        wh = a[1 if y >= 0 else 0]*y + b[1 if z >= 0 else 0]*z
        # |t+w| <= theta < 1 supplies a certified, generous candidate interval.
        first = max(-bound, (-wh).__floor__()-1)
        last = min(bound, (-wl).__ceil__()+1)
        return [t for t in range(first, last+1)
                if sign((r*z-(r-1), t-r*y, y)) <= 0
                and sign((r*z+(r-1), t-r*y, y)) >= 0]

    states = [(z, y) for z in range(-r, r+1) for y in range(-r, r+1)]
    edges = {u: [(u[1], t) for t in digits(*u)] for u in states}
    predecessors = {u: [] for u in states}
    for u, row in edges.items():
        for v in row:
            predecessors[v].append(u)
    radius = (r-2)//3
    ranks = {u: 0 if max(map(abs, u)) <= radius else -1 for u in states}
    queue = deque(u for u in states if ranks[u] == 0)
    while queue:
        v = queue.popleft()
        for u in predecessors[v]:
            if ranks[u] == -1:
                ranks[u] = ranks[v]+1
                queue.append(u)
    return edges, ranks, digits, sign


def energy_delta(r: int, z: int, y: int, t: int) -> tuple[int, int, int]:
    """beta*(Q(y,t)-Q(z,y)), using beta*A=beta^2-r*beta."""
    cross = y*t-z*y
    return r*(y*y-z*z), t*t-y*y-r*cross, cross


def check_parameter(r: int, native: dict[tuple[int, int], tuple[int, int]]) -> dict:
    edges, ranks, digits, sign = graph(r)
    if native.keys() != ranks.keys():
        raise ValueError(f"incomplete or foreign native state coverage at r={r}")
    for u, (rank, selected) in native.items():
        if rank != ranks[u]:
            raise ValueError(f"native rank mismatch: r={r}, pair={u}")
        if rank > 0:
            v = (u[1], selected)
            if v not in edges[u] or ranks[v] != rank-1:
                raise ValueError("native selected digit is not a descending edge")
        elif selected != 0:
            raise ValueError("terminal/uncovered state has a spurious witness")

    def drop(z: int, y: int, depth: int, accumulated=(0, 0, 0)) -> bool:
        if depth == 0:
            return False
        for t in digits(z, y, 2*r):
            delta = energy_delta(r, z, y, t)
            total = tuple(x+y for x, y in zip(accumulated, delta, strict=True))
            if sign(total) < 0 or drop(y, t, depth-1, total):
                return True
        return False

    disk = [u for u in ranks if u[0]**2+u[1]**2 < r*r]
    failures = []
    for z, y in disk:
        if ranks[z, y] < 0:
            raise ValueError("strict-disk source is uncovered")
        if (z, y) == (0, 0) or drop(z, y, 1):
            continue
        failures.append((z, y))
        if y != 0:
            n = r//3
            exceptional = {(n-1,n), (1-n,-n), (n+2,-n), (-n-2,n)}
            if r % 3 or (z, y) not in exceptional:
                raise ValueError("unexpected nonaxis obstruction to one-step descent")
        if (z, y) not in {(1, 0), (-1, 0)} and not drop(z, y, 3):
            raise ValueError("nonterminal disk source has no three-step descent")
    return {
        "r": r, "square_states": len(ranks), "edges": sum(map(len, edges.values())),
        "disk_pairs": len(disk), "uncovered_disk": 0,
        "uncovered_square": sum(v == -1 for v in ranks.values()),
        "max_disk_rank": max(ranks[u] for u in disk),
        "one_step_failures": len(failures),
        "nonaxis_one_step_failures": [list(u) for u in failures if u[1] != 0],
    }


def read_native(path: Path) -> dict[int, dict[tuple[int, int], tuple[int, int]]]:
    out: dict[int, dict] = {}
    with path.open(newline="") as handle:
        rows = csv.DictReader(line for line in handle if not line.startswith("#"))
        if rows.fieldnames != ["r", "z", "y", "rank", "next_t"]:
            raise ValueError("unexpected native CSV schema")
        for row in rows:
            r, z, y, rank, selected = (int(row[key]) for key in rows.fieldnames)
            if r not in PARAMETERS:
                raise ValueError("parameter outside the declared finite replay")
            values = out.setdefault(r, {})
            if (z, y) in values:
                raise ValueError("duplicate native state")
            values[z, y] = rank, selected
    if set(out) != set(PARAMETERS):
        raise ValueError("missing parameter section")
    return out


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--native-csv", type=Path, required=True)
    args = parser.parse_args()
    native = read_native(args.native_csv)
    receipts = [check_parameter(r, native[r]) for r in PARAMETERS]
    print(json.dumps({
        "status": "passed", "scope": "finite sampled parameters; not a uniform theorem",
        "native_sha256": hashlib.sha256(args.native_csv.read_bytes()).hexdigest(),
        "parameters": receipts,
        "total_square_states": sum(v["square_states"] for v in receipts),
        "total_disk_pairs": sum(v["disk_pairs"] for v in receipts),
    }, indent=2))


if __name__ == "__main__":
    main()
