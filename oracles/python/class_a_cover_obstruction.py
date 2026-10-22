"""Independent finite Fraction-field calibration of the Mojo formal cover escape.

Rebuilds the complete seed graphs at n=4,18; neither their finite nonmembership
nor this calibration replaces the written arbitrary-n countermodel proof.
"""
from fractions import Fraction
import json
from class_a_run_index import reference_graph


def calibrate(n):
    g = reference_graph(n)
    def state(a, b, w):
        return a, b, tuple(sum(Fraction(x)*g.l[i][j] for i, x in enumerate(w))
                           for j in range(3))
    source = state(1, 2, (-n-1, n+4, -2))
    target = state(1, 3, (-n, n+3, -1))
    F = g.F
    child = (g.sigma[1][0], g.sigma[2][3],
             F.sub(F.add(F.mul(F.beta, source[2]), g.prefix[2,3]), g.prefix[1,0]))
    if child != target or not g.overlaps(source) or not g.overlaps(target):
        raise ValueError('ordered strict formal edge does not replay')
    if source in g.index or target in g.index:
        raise ValueError('finite nonmembership calibration changed')
    # Mutating just the bottom index must change the actual child displacement.
    altered = F.sub(F.add(F.mul(F.beta, source[2]), g.prefix[2,2]), g.prefix[1,0])
    if altered == target[2]:
        raise ValueError('occurrence mutation was not detected')
    return dict(n=n, complete_seed_vertices=len(g.states), strict_edge_equal=True,
                source_in_seed_graph=False, child_in_seed_graph=False,
                changed_index_detected=True,
                scope='finite calibration; no uniform seed exclusion or BH failure')


if __name__ == '__main__':
    print(json.dumps([calibrate(n) for n in (4,18)], indent=2))
