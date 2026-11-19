"""Census of the vertex-asymptote condition (NM_V) over the unit PIP corpus.

Domain: unit members with at least two periodic letters for both endpoint
maps (necessary for a strict root pair). For each: the members of the zero
fibre (vertex-type from the eventual range, interior-type from the certified
`f`-cycles), and (NM_V) on each side by the exact asymptote decision of
`psc.zero_fibre_asymptotes`. Consistency with round-4 Lemma A is asserted:
a right-side failure needs `g_R` non-injective, a left-side failure `g`
non-injective. `scope:` lines count the members where Theorems UP and UP′ of
the unique-partner note apply (odd determinant, `β₁(ER) ≥ 2`, (NM_V)).
`residual:` lines name every pair of distinct interior members of `F₀` that
are asymptotic on a side: the zero-fibre form of the one configuration left
open by Theorem S of the witness-selection note. Theorem S puts its branch
letters on the collapsed pair of a non-injective endpoint map; that side's map
is asserted non-injective. The census also counts the pairs whose two origin
tiles carry that side's collapsed pair (an observation, not asserted). Finite corpus evidence only; no strict carrier
exists in the corpus.
"""

from psc.c4_geometric_f import PrototileMap, StableRadiiCache
from psc.corpus import pip_corpus
from psc.h1_census import eventual_range, legal_two_words
from psc.zero_fibre_asymptotes import nmv_report


def periodic_count(f: List[Int]) -> Int:
    var n = 0
    for x in range(3):
        var y = x
        for _ in range(3):
            y = f[y]
        var z = y
        var back = False
        for _ in range(3):
            z = f[z]
            back = back or z == x
        n += Int(back)
    return n


def injective(f: List[Int]) -> Bool:
    return f[0] != f[1] and f[0] != f[2] and f[1] != f[2]


def collapsed_pair(f: List[Int]) -> Int:
    """`3 * a + b` for the unique `a < b` with `f[a] == f[b]`, or -1 if injective.
    Only called on maps with two periodic letters, where the pair is unique."""
    for a in range(3):
        for b in range(a + 1, 3):
            if f[a] == f[b]:
                return 3 * a + b
    return -1


def main() raises:
    var corpus = pip_corpus()
    var boxes = StableRadiiCache()
    var domain = 0
    var holds = 0
    var left_fail = 0
    var right_fail = 0
    var scope = 0
    var scope_holds = 0
    var residual = 0
    var scope_residual = 0
    var residual_pairs = 0
    var on_collapsed = 0
    for s in range(len(corpus)):
        var det = corpus[s].incidence.det()
        if det != 1 and det != -1:
            continue
        var sigma = corpus[s].sigma.copy()
        var g = [sigma[a][0] for a in range(3)]
        var gr = [sigma[a][len(sigma[a]) - 1] for a in range(3)]
        if periodic_count(g) < 2 or periodic_count(gr) < 2:
            continue
        domain += 1
        var er = eventual_range(sigma, legal_two_words(sigma))
        var edges = 0
        var lefts = List[Bool](length=3, fill=False)
        var rights = List[Bool](length=3, fill=False)
        for b in range(3):
            for a in range(3):
                if er[3 * b + a]:
                    edges += 1
                    lefts[b] = True
                    rights[a] = True
        var verts = 0
        for x in range(3):
            verts += Int(lefts[x]) + Int(rights[x])
        var beta1 = edges - verts + 1
        var m = PrototileMap(sigma)
        var r = nmv_report(m, boxes)
        if len(r.left_failures) > 0 and injective(g):
            raise Error("Lemma A violated on the left: " + corpus[s].label())
        if len(r.right_failures) > 0 and injective(gr):
            raise Error("Lemma A violated on the right: " + corpus[s].label())
        holds += Int(r.holds())
        left_fail += Int(len(r.left_failures) > 0)
        right_fail += Int(len(r.right_failures) > 0)
        var in_scope = beta1 >= 2
        scope += Int(in_scope)
        scope_holds += Int(in_scope and r.holds())
        if len(r.left_interior) > 0 and injective(g):
            raise Error("Theorem S violated on the left: " + corpus[s].label())
        if len(r.right_interior) > 0 and injective(gr):
            raise Error("Theorem S violated on the right: " + corpus[s].label())
        for k in r.left_interior_letters:
            residual_pairs += 1
            on_collapsed += Int(k == collapsed_pair(g))
        for k in r.right_interior_letters:
            residual_pairs += 1
            on_collapsed += Int(k == collapsed_pair(gr))
        var has_residual = len(r.left_interior) + len(r.right_interior) > 0
        residual += Int(has_residual)
        scope_residual += Int(in_scope and r.holds() and has_residual)
        if has_residual:
            var line = String("residual: ", corpus[s].label(), " det ", det, " sigma ", sigma, " b1 ", beta1,
                              " nmv ", r.holds())
            for f in r.left_interior:
                line += String(" [L ", f, "]")
            for f in r.right_interior:
                line += String(" [R ", f, "]")
            print(line)
        if not r.holds():
            var line = String("fail: ", corpus[s].label(), " det ", det, " sigma ", sigma, " b1 ", beta1,
                              " members ", r.members, " interior ", r.interior)
            for f in r.left_failures:
                line += String(" [L ", f, "]")
            for f in r.right_failures:
                line += String(" [R ", f, "]")
            print(line)
    print("domain (unit, >=2 periodic letters on both sides)", domain)
    print("NM_V holds", holds, "left failures", left_fail, "right failures", right_fail)
    print("scope: beta1 >= 2", scope, "of which NM_V holds", scope_holds)
    print("residual: interior asymptotes in F0 on", residual, "domain members;", scope_residual, "in scope")
    print("residual: origin tiles carry the collapsed pair of that side in", on_collapsed, "of", residual_pairs, "pairs")
