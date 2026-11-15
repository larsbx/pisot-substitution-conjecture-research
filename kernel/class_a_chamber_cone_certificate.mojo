"""Certificate (Theorem CA): boundary hitting on `{t <= 5} ∪ {t <= k - 1}` of the minus class-A chamber, by symbolic cones.

docs/class-a-chamber-entry-stopgo-2026-11-15.md. The minus class-A chamber is

    sigma(x) = x y^A x,   sigma(c) = c y^n x,   sigma(y) = x y^(n-1) c,

`n = k + t + 3`, `d = k + 2t + 5`, `A = n + d = 3n - (k + 1)`, `k, t >= 0`: in
Theorem E's class-A normal form `(p, q, r) = (A, n, n - 1)`, so
`t = p - 2q - 2` and `k = 3q - p - 1`. With `K = k + 1` its sectors are
`D = floor((n - 1) / K)`; `D = 1` is `t <= k - 1`.

The families (`chamber_families`), every one a family of the class-B cone
cover (`class_b_cone_certificate.cover`, with `cls = CLASS_A`):

- `t=c`, `c = 0..5`: the lines `p = 2q + c + 2`, `q >= c + 3` (every `k >= 0`);
- `sector`: `(q, p) = (21, 50) + s1 (1, 2) + s2 (2, 5)`, which is exactly
  `t >= 6`, `k - t >= 6` (unimodular generators: every lattice point);
- `k-t=m`, `m = 1..5`: the lines `(q, p) = (m + 3, 2m + 8) + s (2, 5)`,
  `s = k - m >= 0`.

Together they contain exactly `{t <= 5} ∪ {t <= k - 1}` (`coverage`, checked by
an exact membership solve). For every member of each family, `cover` proves that
every overlap reachable from a swap seed has an offset-zero descendant: symbolic
regions by Lemma S′ of docs/p1b-symbolic-cone-2026-10-08.md, with Lemma S″ of the
note for the cone engine's Bernstein rule, which the class-A cones use; the
points below them by the exact kernel. The set is the sector `D = 1` together
with the six low lines, which reach `D <= 7` where `k < t + 1`. Every chamber
member is PIP; a member the cover counts as not PIP refuses the run.

Usage: `mojo run -I . class_a_chamber_cone_certificate.mojo [all | coverage | <family>]`
(default `all`), or `pixi run class-a-chamber-cone-certificate`.
"""

from std.sys import argv
from psc.pisot import CubicScreen
from a1_normal_form_census import CLASS_A
from class_b_cone_certificate import Aff, CoverTally, Family, contains, cover


def chamber_member(k: Int, t: Int) -> List[Int]:
    """`(p, q, r)` of the chamber member `(k, t)`."""
    var n = k + t + 3
    return [3 * n - (k + 1), n, n - 1]


def chamber_families() -> List[Family]:
    var out = List[Family]()
    for c in range(6):
        out.append(Family("t=" + String(c), Aff(3 * c + 8, 2, 0), Aff(c + 3, 1, 0), Aff(c + 2, 1, 0), 0, 0, CLASS_A))
    out.append(Family("sector", Aff(50, 2, 5), Aff(21, 1, 2), Aff(20, 1, 2), 0, 0, CLASS_A))
    for m in range(1, 6):
        out.append(Family("k-t=" + String(m), Aff(2 * m + 8, 5, 0), Aff(m + 3, 2, 0), Aff(m + 2, 2, 0), 0, 0, CLASS_A))
    return out^


def claimed(k: Int, t: Int) -> Bool:
    return t <= 5 or t <= k - 1


def coverage(fams: List[Family], bound: Int) -> List[Int]:
    """`[missed, stray]` over `0 <= k, t <= bound`: claimed points that no family
    contains, and unclaimed points that some family contains."""
    var missed = 0
    var stray = 0
    for k in range(bound + 1):
        for t in range(bound + 1):
            var m = chamber_member(k, t)
            var hit = False
            for i in range(len(fams)):
                if contains(fams[i], m[0], m[1], m[2]):
                    hit = True
                    break
            if claimed(k, t) and not hit:
                missed += 1
            if not claimed(k, t) and hit:
                stray += 1
    return [missed, stray]


def main() raises:
    var args = argv()
    var which = String(args[1]) if len(args) > 1 else "all"
    var all = chamber_families()
    if which == "coverage":
        var gaps = coverage(all, 200)
        print("coverage up to k, t = 200: missed", gaps[0], " stray", gaps[1])
        if gaps[0] != 0 or gaps[1] != 0:
            raise Error("the families do not cover exactly t <= 5 or t <= k - 1")
        return
    var fams = List[Family]()
    for i in range(len(all)):
        if which == "all" or all[i].name == which:
            fams.append(all[i].copy())
    if len(fams) == 0:
        raise Error("unknown family ", which)
    var screen = CubicScreen()
    var tally = CoverTally(True)
    for i in range(len(fams)):
        cover(fams[i], screen, tally)
    print("regions", tally.regions, "finite", tally.finite, "non-PIP", tally.non_pip, "largest", tally.largest)
    if tally.non_pip != 0:
        raise Error("a chamber member was counted not PIP: the family premise fails")
