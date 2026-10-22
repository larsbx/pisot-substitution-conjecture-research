"""Generate the potential pieces and descent occurrences of the typed class-A carrier.

Input: exact complete seed-graph exports `graph-n{n}.log` for n = NLO..24, as
written by `kernel/class_a_run_index.mojo export N` (V/E/SEED/SUMMARY records
with zero-based occurrence indices and first offset-zero depths). Output: the
tables of `kernel/psc/class_a_descent_data.mojo`, also written as JSON.

This is a *generator*, not a proof: it fits, on each carrier row, affine
sub-intervals (pieces) on which the exact first-hit depth equals
floor((a n + b j + c)/3), splits the offset-zero target into its own piece,
and chooses for every non-target piece one symbolic child occurrence type
(top segment, bottom segment, child y) that lowers X = a n + b j + c at every
sampled member, splitting further where the child's piece changes. Every row
it emits is then proved for all n >= NLO by `psc.class_a_carrier_descent`
and re-proved by `oracles/python/class_a_carrier_closure.py`.

  python oracles/python/class_a_descent_table.py GRAPH_DIR [NLO=8] [--mojo OUT]
  python oracles/python/class_a_descent_table.py GRAPH_DIR NLO --line minus --rows-mojo OUT
  python oracles/python/class_a_descent_table.py GRAPH_DIR NLO --line minus [--mojo OUT]

`--line minus` reads exports of the minus line (n+1,n,n-1) from
`kernel/class_a_minus_line.mojo export N`, takes its carrier rows from
`kernel/psc/class_a_minus_carrier.mojo`; `--rows-mojo OUT` instead only
*infers* those rows and stops: group the labels of every export by (top, bottom, s, y),
coalesce consecutive k into maximal runs, and fit each run endpoint as an
affine form a n + b, refusing unless every export NLO..24 agrees exactly.
"""
from pathlib import Path
from collections import defaultdict
import json
import re
import sys

ROOT = Path(__file__).resolve().parents[2]
FIRST = {0: 0, 1: 1, 2: 0}
LAST = {0: 0, 1: 0, 2: 1}


def _opt(name):
    return sys.argv[sys.argv.index(name) + 1] if name in sys.argv else None


OPTS = {"--line", "--rows-mojo", "--mojo"}
ARGS = [a for i, a in enumerate(sys.argv[1:], 1) if not a.startswith("--") and sys.argv[i - 1] not in OPTS]
EPS = {"plus": 1, "minus": -1}[_opt("--line") or "plus"]
SRC = ROOT / ("kernel/psc/class_a_typed_carrier.mojo" if EPS == 1 else "kernel/psc/class_a_minus_carrier.mojo")
ROW_COUNT = 89 if EPS == 1 else 104
DATA_NAME = "class_a_descent_data" if EPS == 1 else "class_a_minus_descent_data"
PREFIX = "" if EPS == 1 else "minus_"
G = Path(ARGS[0]) if ARGS else ROOT / "evidence/class-a-carrier-closure-2026-10-22/graphs"
NLO = int(ARGS[1]) if len(ARGS) > 1 else 8
NS = list(range(NLO, 25))


def rows():
    m = re.findall(r"^\s+List\[Int\]\(\[(-?\d+(?:,-?\d+){7})\]\),$", SRC.read_text(), re.M)
    out = [tuple(map(int, x.split(","))) for x in m]
    if len(out) != ROW_COUNT:
        raise ValueError("expected %d carrier rows" % ROW_COUNT)
    return out


def infer_rows():
    """Affine typed rows fitted to every export NLO..24; refuses on any disagreement."""
    lab = defaultdict(lambda: defaultdict(list))
    for n in NS:
        for line in (G / f"graph-n{n}.log").read_text().splitlines():
            p = line.split()
            if p and p[0] == "V":
                _, _, t, b, k, c, y, _ = map(int, p[1:])
                lab[(t, b, k + c + y, y)][n].append(k)
    out = []
    for key in sorted(lab):
        runs = {}
        for n in NS:
            rs = []
            for k in sorted(lab[key].get(n, [])):
                if rs and k == rs[-1][1] + 1:
                    rs[-1][1] = k
                else:
                    rs.append([k, k])
            runs[n] = rs
        if len({len(v) for v in runs.values()}) != 1:
            raise RuntimeError("run count of slice %s varies with n" % (key,))
        for i in range(len(runs[NS[0]])):
            fit = []
            for e in (0, 1):
                a = runs[NS[1]][i][e] - runs[NS[0]][i][e]
                b = runs[NS[0]][i][e] - a * NS[0]
                if any(runs[n][i][e] != a * n + b for n in NS):
                    raise RuntimeError("row endpoint of slice %s is not affine" % (key,))
                fit += [a, b]
            out.append(key + tuple(fit))
    return out


if _opt("--rows-mojo"):
    inferred = infer_rows()
    body = "\n".join("        List[Int]([%s])," % ",".join(map(str, r)) for r in inferred)
    Path(_opt("--rows-mojo")).write_text('''"""Typed affine carrier of the class-A minus line `(n+1, n, n-1)` (#139).

Rows `(top, bottom, s, y, a, b, c, d)` contain the labels `(top, bottom, w)`
with `w = (k, s-k-y, y)` and `a n + b <= k <= c n + d`. The %d rows in %d
typed slices were synthesized by `oracles/python/class_a_descent_table.py
--line minus` from exact complete seed graphs n=%d..24; they are a proof
*target* and evidence only through `psc.class_a_carrier_closure.certify_closure_line`.
Source note: docs/class-a-minus-line-2026-10-22.md.
"""


def minus_rows() -> List[List[Int]]:
    """Rows: top,bottom,sum(w),w_y,k_lower_slope,k_lower_constant,k_upper_slope,k_upper_constant."""
    return List[List[Int]]([
%s
    ])
''' % (len(inferred), len({r[:4] for r in inferred}), NLO, body))
    print("rows:", len(inferred), "slices:", len({r[:4] for r in inferred}), file=sys.stderr)
    raise SystemExit(0)
R = rows()


def load_full(n):
    V, E = {}, defaultdict(list)
    lab = {}
    for line in (G / f"graph-n{n}.log").read_text().splitlines():
        p = line.split()
        if not p: continue
        if p[0] == "V":
            _, i, t, b, k, c, y, d = map(int, p[1:]); lab[i] = (t,b,k,c,y); V[(t,b,k,c,y)] = d
        elif p[0] == "E":
            _, a, b2, i, j = map(int, p[1:]); E[a].append((b2, i, j))
    edges = defaultdict(set)   # parent label -> set of (child label, part_t, part_b)
    run = {0: n+1, 1: n, 2: n+EPS}
    for a, lst in E.items():
        t, b = lab[a][0], lab[a][1]
        for b2, i, j in lst:
            pt = 0 if i == 0 else (1 if i <= run[t] else 2)
            pb = 0 if j == 0 else (1 if j <= run[b] else 2)
            edges[lab[a]].add((lab[b2], pt, pb))
    return V, edges

DATA = {n: load_full(n) for n in NS}

def row_members(ri, n):
    t,b,s,y,al,bl,au,bu = R[ri]
    return [(t,b,k,s-k-y,y) for k in range(al*n+bl, au*n+bu+1)]

def floor_fit(points, slack=0):
    """points: list of (n, j, depth). return (a,b,c) with
    depth <= floor((a n + b j + c)/3) <= depth + slack, or None. slack=0 is the exact fit;
    a positive slack only over-estimates the depth, which the verifier never relies on."""
    for a in range(-3, 4):
        for b in range(-3, 4):
            lo, hi = -10**9, 10**9
            for n, j, d in points:
                base = 3*d - a*n - b*j
                lo = max(lo, base); hi = min(hi, base+2+3*slack)
            if lo <= hi: return (a, b, lo)
    return None

# ---- pieces per row: greedy split with affine-in-n breakpoints ----
def pieces_of_row(ri, slack=0):
    t,b,s,y,al,bl,au,bu = R[ri]
    Jrow = (au-al, bu-bl)
    members = {n: row_members(ri, n) for n in NS}
    depth = {n: [DATA[n][0][m] for m in members[n]] for n in NS}
    def search(start, END):
        J = lambda n: END[0]*n + END[1]
        slo = lambda n: start[0]*n + start[1]
        if all(slo(n) > J(n) for n in NS): return []
        cands = []
        for alpha, beta in [(a_, b_) for a_ in (-1, 0, 1) for b_ in range(-6, 7)] + [END]:
            if any(alpha*n+beta < slo(n) for n in NS): continue
            if not (all(alpha*n+beta >= J(n) for n in NS) or all(alpha*n+beta <= J(n) for n in NS)): continue
            phi = lambda n, alpha=alpha, beta=beta: min(alpha*n+beta, J(n))
            pts = [(n, j, depth[n][j]) for n in NS for j in range(slo(n), phi(n)+1) if phi(n) >= slo(n)]
            fit = floor_fit(pts, slack)
            if fit:
                up = END if all(alpha*n+beta >= J(n) for n in NS) else (alpha, beta)
                cands.append((sum(max(0, phi(n)-slo(n)+1) for n in NS), up, fit))
        cands.sort(key=lambda c: -c[0])
        seen = set()
        for _, up, fit in cands:
            if up in seen: continue
            seen.add(up)
            rest = search((up[0], up[1]+1), END)
            if rest is not None: return [(start, up, fit)] + rest
        return None
    if s == 0 and y == 0 and all(al*n+bl <= 0 <= au*n+bu for n in NS):
        j0 = (-al, -bl)
        left = search((0, 0), (j0[0], j0[1]-1))
        right = search((j0[0], j0[1]+1), Jrow)
        if left is None or right is None: return None
        return left + [(j0, j0, (0, 0, 0))] + right
    return search((0, 0), Jrow)


SLACK_ROWS = []


def row_pieces(ri):
    """Exact depth fit first; only a row with no exact fit retries with slack 1."""
    for slack in (0, 1):
        out = pieces_of_row(ri, slack)
        if out is not None:
            if slack:
                SLACK_ROWS.append(ri)
                print("row", ri, "fitted with slack", slack, file=sys.stderr)
            return out
    raise RuntimeError("no piece partition for row %d" % ri)

PIECES = []  # (ri, lo, hi, (a,b,c))
for ri in range(len(R)):
    for lo, hi, fit in row_pieces(ri):
        PIECES.append((ri, lo, hi, fit))
print("pieces:", len(PIECES), file=sys.stderr)

def piece_of(label, n):
    t,b,k,c,y = label; s = k+c+y
    for pi, (ri, lo, hi, fit) in enumerate(PIECES):
        rt,rb,rs,ry,al,bl,au,bu = R[ri]
        if (rt,rb,rs,ry) != (t,b,s,y): continue
        j = k - (al*n+bl)
        if lo[0]*n+lo[1] <= j <= hi[0]*n+hi[1]: return pi, j
    raise KeyError(label)

def X(pi, n, j):
    a,b,c = PIECES[pi][3]; return a*n + b*j + c

# ---- Stage B/C: type-uniform affine sub-intervals, then child-piece splits ----
def le(u,v): return u[0]<=v[0] and u[0]*NLO+u[1] <= v[0]*NLO+v[1]

def good_types(pi, n, j):
    ri, lo, hi, fit = PIECES[pi]; t,b,s,y,al,bl,au,bu = R[ri]
    k = al*n+bl+j; lab=(t,b,k,s-k-y,y); xs = X(pi,n,j)
    out = {}
    for child, pt, pb in DATA[n][1].get(lab, ()):
        cpi, cj = piece_of(child, n)
        if X(cpi,n,cj) <= xs-1: out[(pt,pb,child[4])] = cpi
    return out

def is_target_piece(pi):
    ri, lo, hi, fit = PIECES[pi]; t,b,s,y,al,bl,au,bu = R[ri]
    return s == 0 and y == 0 and lo == hi and (al+lo[0], bl+lo[1]) == (0, 0)

GT = {}
def gt(pi, n, j):
    key = (pi, n, j)
    if key not in GT: GT[key] = good_types(pi, n, j)
    return GT[key]

def type_partition(pi):
    """partition piece pi's j-range into affine sub-intervals each with one uniform good type."""
    ri, lo, hi, fit = PIECES[pi]
    def search(start):
        slo = lambda n: start[0]*n + start[1]
        if all(slo(n) > hi[0]*n+hi[1] for n in NS): return []
        cands = []
        ends = ([(a_, b_) for a_ in (-1, 0, 1) for b_ in range(-6, 7)] + [hi, (start[0], start[1]), (start[0], start[1]+1), (start[0], start[1]+2)]
                + [(hi[0], hi[1]-1), (hi[0], hi[1]-2)])   # a piece end of slope 2 (the minus line's width-2n row)
        for alpha, beta in ends:
            if any(alpha*n+beta < slo(n) for n in NS): continue
            if not (all(alpha*n+beta >= hi[0]*n+hi[1] for n in NS) or all(alpha*n+beta <= hi[0]*n+hi[1] for n in NS)): continue
            up = hi if all(alpha*n+beta >= hi[0]*n+hi[1] for n in NS) else (alpha, beta)
            common = None
            for n in NS:
                for j in range(slo(n), up[0]*n+up[1]+1):
                    g = set(gt(pi, n, j)); common = g if common is None else common & g
                    if not common: break
                if common is not None and not common: break
            if common:
                cands.append((sum(max(0, up[0]*n+up[1]-slo(n)+1) for n in NS), up, sorted(common)))
        cands.sort(key=lambda c: -c[0])
        seen=set()
        for _, up, types in cands:
            if up in seen: continue
            seen.add(up)
            rest = search((up[0], up[1]+1))
            if rest is not None: return [(start, up, types)] + rest
        return None
    return search(lo)

DESCENT = []   # (pi, sub_lo, sub_hi, (pt,pb,yp), child_pi)
failures = 0
for pi, (ri, lo, hi, fit) in enumerate(PIECES):
    if is_target_piece(pi): continue
    t,b,s,y,al,bl,au,bu = R[ri]
    part = type_partition(pi)
    if part is None:
        failures += 1; print("NO TYPE PARTITION: piece", pi, R[ri][:4], lo, hi, fit); continue
    for (slo, shi, types) in part:
        # choose the type with fewest child pieces
        best = None
        for ty in types:
            kids = set(gt(pi, n, j)[ty] for n in NS for j in range(slo[0]*n+slo[1], shi[0]*n+shi[1]+1))
            if best is None or len(kids) < len(best[1]): best = (ty, kids)
        ty, kids = best
        pt, pb, yp = ty
        dx = (1 if FIRST[b]==0 else 0)*(pb>0) - (1 if FIRST[t]==0 else 0)*(pt>0)
        k0 = (al, bl + s + dx)
        for cpi in sorted(kids):
            cri, clo, chi, cfit = PIECES[cpi]
            cal, cbl = R[cri][4], R[cri][5]
            sl = (clo[0]+cal-k0[0], clo[1]+cbl-k0[1]); sh = (chi[0]+cal-k0[0], chi[1]+cbl-k0[1])
            L_ = slo if le(sl, slo) else (sl if le(slo, sl) else None)
            H_ = shi if le(shi, sh) else (sh if le(sh, shi) else None)
            if L_ is None or H_ is None:
                failures += 1; print("CLIP INCOMPARABLE piece", pi, "child", cpi, sl, sh, slo, shi); continue
            DESCENT.append((pi, L_, H_, ty, cpi))
print("NLO", NLO, "pieces", len(PIECES), "failures:", failures, " descent rows:", len(DESCENT), file=sys.stderr)
import json
TABLE = {"nlo": NLO, "pieces": [(ri, lo, hi, fit) for ri, lo, hi, fit in PIECES],
         "descent": [(pi, lo, hi, list(ty), cpi) for pi, lo, hi, ty, cpi in DESCENT]}
if failures:
    raise SystemExit("incomplete descent table")
print(json.dumps(TABLE))
if "--mojo" in sys.argv:
    out = Path(_opt("--mojo"))
    what = "" if EPS == 1 else " of the minus line (n+1,n,n-1)"
    lines = ['"""Affine potential pieces and chosen descent occurrences of the typed class-A carrier%s.' % what,
             "", "Generated from exact complete seed graphs n=%d..24 (BFS first-hit depths, with" % NLO,
             "potential X = a n + b j + c satisfying depth = floor(X/3) on each piece), then",
             "verified symbolically for every n>=%d by `psc.class_a_carrier_descent`. The" % NLO,
             "tables are a proof *target*; nothing here is evidence until that verifier",
             "accepts every row. Regenerate with oracles/python/class_a_descent_table.py."]
    if SLACK_ROWS:
        lines += ["", "Carrier row(s) %s admit no exact fit (the first-hit plateaus shift with n mod 3);" % ", ".join(map(str, SLACK_ROWS)),
                  "there the potential only satisfies depth <= floor(X/3) <= depth + 1."]
    lines += ['"""', "", "",
             "def %spiece_rows() -> List[List[Int]]:" % PREFIX,
             '    """[carrier row, j_lo slope, j_lo constant, j_hi slope, j_hi constant, X_n, X_j, X_c]."""',
             "    return List[List[Int]](["]
    lines += ["        List[Int]([%d,%d,%d,%d,%d,%d,%d,%d])," % (ri, lo[0], lo[1], hi[0], hi[1], fit[0], fit[1], fit[2]) for ri, lo, hi, fit in PIECES]
    lines += ["    ])", "", "", "def %sdescent_rows() -> List[List[Int]]:" % PREFIX,
              '    """[piece, j_lo slope, j_lo constant, j_hi slope, j_hi constant, top part, bottom part, child y, child piece]."""',
              "    return List[List[Int]](["]
    lines += ["        List[Int]([%d,%d,%d,%d,%d,%d,%d,%d,%d])," % (pi, lo[0], lo[1], hi[0], hi[1], ty[0], ty[1], ty[2], cpi) for pi, lo, hi, ty, cpi in DESCENT]
    lines += ["    ])"]
    out.write_text("\n".join(lines) + "\n")
