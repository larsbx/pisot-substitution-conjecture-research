"""Exact census: can every recurrent vertex reach a catch-up hit?

For each standing-corpus specimen, `psc.one_tile` builds the box graph and
counts its recurrent non-offset-zero vertices, those in CU (leftmost chain
reaches offset zero: a one-tile boundary hit) and those with a descendant in
CU (some catch-up hit is reachable). A specimen *fails Q1* when some recurrent
vertex reaches no catch-up hit: there, every new common vertex it can reach
is a simultaneous birth, and the one-tile reduction of the cross-letter
rigidity fails (docs/p1b-vertex-coincidence-box-2026-10-02.md §5.6b).
Each failing specimen is re-checked two-sidedly (`psc.one_tile.two_sided`):
a recurrent vertex is rescued if its mirror image reaches a catch-up of the
mirror substitution `sigma~` (every image word reversed; same incidence
matrix), i.e. a right-endpoint catch-up of `sigma`. A specimen *fails at both
endpoints* when some recurrent vertex reaches a catch-up at neither. Each specimen is
also tested for Lemma P's arithmetic obstruction (`catch_up_free`), which
forces total failure; the census checks the lemma's conclusion (no vertex in
CU) and counts total failures it does not explain. Folded in canonical order on `parallel_fold`.
"""

from parallel_fold.map_fold import parallel_map_fold
from psc.corpus import Specimen, pip_corpus
from psc.one_tile import catch_up_free, one_tile, two_sided

comptime WORKERS = 4


struct OneTileCensus(Copyable, Movable):
    var specimens: Int
    var recurrent: Int
    var in_cu: Int
    var reach_cu: Int
    var fails: List[Int]
    var none_reach: Int
    var both: List[Int]
    var both_none: Int
    var free: Int
    var free_total: Int
    var total_not_free: Int
    var failed_index: Int

    def __init__(out self):
        self.specimens = 0
        self.recurrent = 0
        self.in_cu = 0
        self.reach_cu = 0
        self.fails = List[Int]()
        self.none_reach = 0
        self.both = List[Int]()
        self.both_none = 0
        self.free = 0
        self.free_total = 0
        self.total_not_free = 0
        self.failed_index = -1


def merge(a: OneTileCensus, b: OneTileCensus) -> OneTileCensus:
    var out = a.copy()
    out.specimens += b.specimens
    out.recurrent += b.recurrent
    out.in_cu += b.in_cu
    out.reach_cu += b.reach_cu
    for i in range(len(b.fails)):
        out.fails.append(b.fails[i])
    out.none_reach += b.none_reach
    for i in range(len(b.both)):
        out.both.append(b.both[i])
    out.both_none += b.both_none
    out.free += b.free
    out.free_total += b.free_total
    out.total_not_free += b.total_not_free
    if b.failed_index >= 0 and (out.failed_index < 0 or b.failed_index < out.failed_index):
        out.failed_index = b.failed_index
    return out^


def main() raises:
    var corpus = pip_corpus()

    def one(s: Int) {corpus} -> OneTileCensus:
        var out = OneTileCensus()
        out.specimens = 1
        try:
            var v = one_tile(corpus[s].sigma)
            out.recurrent = v.recurrent
            out.in_cu = v.in_cu
            out.reach_cu = v.reach_cu
            var free = catch_up_free(corpus[s].sigma)
            var total = v.recurrent > 0 and v.reach_cu == 0
            if free:
                if v.in_cu != 0:
                    raise Error("Lemma P violated: a catch-up-free specimen has a vertex in CU")
                out.free = 1
                if total:
                    out.free_total = 1
            elif total:
                out.total_not_free = 1
            if v.reach_cu < v.recurrent:
                out.fails.append(s)
                if v.reach_cu == 0:
                    out.none_reach = 1
                var t = two_sided(corpus[s].sigma)
                if t.reach_either < t.recurrent:
                    out.both.append(s)
                    if t.reach_either == 0:
                        out.both_none = 1
        except:
            out.failed_index = s
        return out^

    var r = parallel_map_fold(one, merge, OneTileCensus(), len(corpus), WORKERS)
    if r.failed_index >= 0:
        _ = one_tile(corpus[r.failed_index].sigma)
        raise Error("one-tile census: worker failure did not replay")
    print("One-tile census, specimens:", r.specimens)
    print("recurrent vertices:", r.recurrent, " in CU:", r.in_cu, " reach CU:", r.reach_cu)
    print("specimens failing Q1:", len(r.fails), " of which no recurrent vertex reaches CU:", r.none_reach)
    print("catch-up-free (no proper prefix in M Z^3):", r.free, " of which Q1 fails totally:", r.free_total, " total failures not catch-up-free:", r.total_not_free)
    print("specimens failing Q1 at both endpoints:", len(r.both), " of which no recurrent vertex reaches either:", r.both_none)
    for i in range(min(len(r.fails), 12)):
        print("Q1 fails:", corpus[r.fails[i]].label())
    for i in range(len(r.both)):
        print("Q1 fails at both endpoints:", corpus[r.both[i]].label(), two_sided(corpus[r.both[i]].sigma))
