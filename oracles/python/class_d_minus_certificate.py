"""Independent integer oracle for the parametric minus-boundary certificate.

This verifies universal polynomial/affine inequalities, not sample agreement.
Mojo is canonical; a successful Python run alone cannot promote the family.
Run from the repository root: python oracles/python/class_d_minus_certificate.py
"""
from pathlib import Path
import json

ROOT = Path(__file__).resolve().parents[2]
DATA = ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json"
# ell_x, ell_c, ell_y multiplied by 2(1+t), t=1/beta in (0,1/10).
LENGTHS = ((3, -2, -4), (3, 0, -2), (2, 2, 0))
RUNS = ((3, 5), (3, 6), (2, 4))
STARTS, ENDS = (0, 1, 1), (1, 0, 1)


def require(condition, message):
    if not condition:
        raise ValueError(message)


def bernstein100(poly):
    """100 times degree-two Bernstein coefficients on [0,1/10]."""
    c, b, a = poly
    return (100*c, 100*c+5*b, 100*c+10*b+a)


def inequalities(label):
    top, bot, *w = label
    shift = [sum(w[j]*LENGTHS[j][i] for j in range(3)) for i in range(3)]
    return ([shift[i]+LENGTHS[bot][i] for i in range(3)],
            [LENGTHS[top][i]-shift[i] for i in range(3)])


def interior(label):
    return all(min(b := bernstein100(p)) >= 0 and max(b) > 0
               for p in inequalities(label))


def impossible(label):
    # A boundary-only contact is excluded too. A merely failed positive
    # certificate is NEVER treated as an impossibility certificate.
    return any(max(bernstein100(p)) <= 0 for p in inequalities(label))


def affine_nonnegative(m, b):
    return m >= 0 and 2*m+b >= 0


def affine_prefix(letter, m, b):
    """Fixed segment valid for every integer a>=2; return letter and prefix."""
    rm, rb = RUNS[letter]
    if (m, b) == (0, 0):
        return STARTS[letter], (0, 0, 0), (0, 0, 0)
    slope, const = [0, 0, 0], [int(STARTS[letter] == k) for k in range(3)]
    if (m, b) == (rm, rb+1):
        slope[2], const[2] = rm, rb
        return ENDS[letter], tuple(slope), tuple(const)
    require(affine_nonnegative(m, b-1) and affine_nonnegative(rm-m, rb-b),
            "occurrence leaves its run for some a>=2")
    slope[2], const[2] = m, b-1
    return 2, tuple(slope), tuple(const)


def segments(letter):
    start = tuple(int(STARTS[letter] == k) for k in range(2))
    m, b = RUNS[letter]
    return ((STARTS[letter], (0, 0), (0, 0), (0, 0)),
            (2, start, (0, 0), (m, b-1)),
            (ENDS[letter], start, (m, b), (m, b)))


def verify(rows):
    require(bool(rows), "empty cover")
    require(all(len(r) == 11 and all(type(x) is int for x in r) for r in rows),
            "invalid certificate row")
    # Same finite input bounds as the checked native integer Mojo consumer.
    require(len(rows) <= 1000, "table budget")
    for r in rows:
        require(0 <= r[0] < 3 and 0 <= r[1] < 3 and
                all(abs(x) <= 100 for x in r[2:5]+r[7:]) and
                0 <= r[5] <= 1000, "invalid label/rank/coefficient")
    labels = [tuple(r[:5]) for r in rows]
    cover = set(labels)
    require(len(cover) == len(rows), "duplicate label")
    require(all(interior(k) for k in labels), "interior inequality unproved")
    seed_count = 0
    for a in range(3):
        for b in range(a+1, 3):
            ea = [int(k == a) for k in range(3)]
            eb = [int(k == b) for k in range(3)]
            seeds = ((a,b,0,0,0), (a,a,*eb), (b,b,*[-x for x in ea]),
                     (b,a,*[eb[k]-ea[k] for k in range(3)]))
            for seed in seeds:
                if impossible(seed):
                    continue
                require(seed in cover, "seed escapes cover")
                seed_count += 1
    candidates = 0
    for k in labels:
        top, bot, x, c, y = k
        if top == bot and (x,c,y) == (0,0,0):
            continue  # coincidences are terminal in the exact seed graph
        mw = (x+c, x+c+2*y)
        mz = (3*x+3*c+2*y, 5*x+6*c+4*y)
        for ct, pt, lt, ht in segments(top):
            for cb, pb, lb, hb in segments(bot):
                u, v = (mw[j]+pb[j]-pt[j] for j in range(2))
                lower = [mz[j]+lb[j]-ht[j] for j in range(2)]
                upper = [mz[j]+hb[j]-lt[j] for j in range(2)]
                # All lengths <=3/2 and ell_y=1 imply |z|<3/2(|u|+|v|+1).
                bound = 3*(abs(u)+abs(v)+1)//2+1
                for z in range(-bound, bound+1):
                    candidates += 1
                    if affine_nonnegative(lower[0], lower[1]-z-1):
                        continue
                    if affine_nonnegative(-upper[0], z-upper[1]-1):
                        continue
                    child = (ct,cb,u,v,z)
                    if impossible(child):
                        continue
                    require(child in cover, f"child escapes cover: {k} -> {child}")
    targets = 0
    for row in rows:
        top, bot, x, c, y, rank, nxt, im, ib, jm, jb = row
        if (x,c,y) == (0,0,0):
            require(rank == 0 and nxt == -1 and (im,ib,jm,jb) == (0,0,0,0),
                    "invalid offset-zero target row")
            targets += 1
            continue
        require(rank > 0 and 0 <= nxt < len(rows) and rows[nxt][5] < rank,
                "no strict rank descent")
        ct, sa, pa = affine_prefix(top, im, ib)
        cb, sb, pb = affine_prefix(bot, jm, jb)
        require((ct,cb) == tuple(rows[nxt][:2]), "wrong occurrence letters")
        slope = (0, 0, 3*x+3*c+2*y)
        const = (x+c, x+c+2*y, 5*x+6*c+4*y)
        require(all(slope[j]+sb[j]-sa[j] == 0 for j in range(3)),
                "affine offset slope does not vanish")
        require([const[j]+pb[j]-pa[j] for j in range(3)] == rows[nxt][2:5],
                "wrong affine child offset")
    return dict(states=len(rows), targets=targets, seed_occurrences=seed_count,
                closure_candidates=candidates, max_rank=max(r[5] for r in rows))


def report():
    data = json.loads(DATA.read_text())
    require((data['branch'], data['b'], data['a_min']) == (-1,0,2), "wrong scope")
    return dict(status="PARAMETRIC_CERTIFICATE_ORACLE_VERIFIED",
                authority="independent-python-oracle", canonical_execution="NOT_RUN_LOCALLY",
                parameter_domain="s=-1, b=0, every integer a>=2",
                universal_branch_status="CANDIDATE_PENDING_CANONICAL_REPLAY",
                positive_branch="OPEN", universal_PSC="OPEN", **verify(data['rows']))


if __name__ == "__main__":
    print(json.dumps(report(), indent=2))
