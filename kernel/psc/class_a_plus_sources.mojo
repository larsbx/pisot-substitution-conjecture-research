"""Original canonical swap intersections for the plus Class-A length order.

Derive all intersections from the literal two-letter words ab and ba.
The c/y middle intersection is y/y because Lc<Ly; the old minus S18
label list is not reused. Callers separately bind their actual family.
"""
from psc.class_a_boundary_children import BoundaryLabel, geometric_state
from psc.class_a_x_ladder import reversed_label
from psc.overlap_seed_patch import SeedOverlapTables, interior_overlap
from psc.perron_field3 import cubic_sub_checked, sign_at_perron


def plus_swap_sources(tables: SeedOverlapTables) raises -> List[BoundaryLabel]:
    if (sign_at_perron(tables.field, tables.lengths.l1) <= 0 or
        sign_at_perron(tables.field, cubic_sub_checked(tables.lengths.l2, tables.lengths.l1)) <= 0 or
        sign_at_perron(tables.field, cubic_sub_checked(tables.lengths.l0, tables.lengths.l2)) <= 0):
        raise Error("plus swap sources require 0<Lc<Ly<Lx")
    var out = List[BoundaryLabel]()
    for pair in [[0, 1], [0, 2], [1, 2]]:
        var a = pair[0]
        var b = pair[1]
        for i in range(2):
            for j in range(2):
                var coordinates = List[Int](length=3, fill=0)
                if j == 1:
                    coordinates[b] += 1
                if i == 1:
                    coordinates[a] -= 1
                var w = BoundaryLabel(a if i == 0 else b, b if j == 0 else a,
                    coordinates[0], coordinates[1], coordinates[2])
                if interior_overlap(tables, geometric_state(tables, w)):
                    for earlier in out:
                        if earlier == w or earlier == reversed_label(w):
                            raise Error("duplicate original plus swap intersection")
                    out.append(w)
                    out.append(reversed_label(w))
    if len(out) != 18:
        raise Error("the actual plus swaps do not have eighteen orientations")
    return out^
