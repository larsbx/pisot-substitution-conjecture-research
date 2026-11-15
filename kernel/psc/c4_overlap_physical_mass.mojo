"""Exact physical overlap budgets in the authenticated Perron length basis."""

from finite_exact.checked_int import checked_add, checked_mul, checked_sub
from finite_exact.rat_q import Q
from psc.c4_overlap_scc_obstruction import canonical_overlap_partition
from psc.c4_pair_overlap_new_incidence import (
    NewIncidenceGraph, authenticate_new_graph, new_matrix_power,
)


comptime LENGTH_GRID = 1000000000


def length_difference(a: List[Int], b: List[Int]) raises -> List[Int]:
    return [checked_sub(a[0], b[0]), checked_sub(a[1], b[1]), checked_sub(a[2], b[2])]


def _length_sign(vector: List[Int], lower: List[Int], upper: List[Int]) raises -> Int:
    if vector[0] == 0 and vector[1] == 0 and vector[2] == 0:
        return 0
    var lo = 0
    var hi = 0
    for k in range(3):
        var x = vector[k]
        lo = checked_add(lo, checked_mul(x, lower[k] if x >= 0 else upper[k]))
        hi = checked_add(hi, checked_mul(x, upper[k] if x >= 0 else lower[k]))
    if lo > 0:
        return 1
    if hi < 0:
        return -1
    raise Error("physical endpoint sign not separated; inconclusive")


def source_loss_witnesses(rows: List[List[Int]], losing: List[Bool], root_count: Int) raises -> List[List[Int]]:
    """Return (component, size, losing vertex) for every inverse source SCC."""
    if len(losing) != len(rows) or root_count < 1 or root_count > len(rows):
        raise Error("physical loss or root inventory size")
    var partition = canonical_overlap_partition(rows)
    var witnesses = List[List[Int]]()
    for c in range(len(partition.members)):
        if len(partition.incoming[c]) != 0:
            continue
        var block = partition.members[c].copy()
        if block[0] >= root_count:
            raise Error("inverse source SCC omits all declared roots")
        var witness = -1
        for vertex in block:
            if losing[vertex]:
                witness = vertex
                break
        if witness < 0:
            raise Error("source SCC has no strictly losing row; inconclusive")
        witnesses.append([c, len(block), witness])
    return witnesses^


def certify_physical_mass(graph: NewIncidenceGraph) raises -> Tuple[List[List[Int]], List[List[Int]], List[List[Int]]]:
    # A missing occurrence can manufacture a false positive deficit.
    authenticate_new_graph(graph)
    var lower: List[Int] = [LENGTH_GRID, 1255773570, 898160951]
    var upper: List[Int] = [LENGTH_GRID, 1255773571, 898160952]
    for k in range(3):
        if lower[k] <= 0 or not Q(Int64(lower[k]), LENGTH_GRID).le(graph.model.chart.ell[k].lo) or not graph.model.chart.ell[k].hi.le(Q(Int64(upper[k]), LENGTH_GRID)):
            raise Error("physical length interval outside the certified grid")
    var mass = List[List[Int]]()
    var zero: List[Int] = [0, 0, 0]
    for state in graph.states:
        if state[0] == state[1] and state[2] == 0 and state[3] == 0 and state[4] == 0:
            raise Error("unexpected fixed track-swap orbit")
        var z: List[Int] = [state[2], state[3], state[4]]
        var minus_z = length_difference(zero, z)
        var a = zero.copy()
        var b = minus_z.copy()
        a[state[0]] = 1
        b[state[1]] = checked_add(b[state[1]], 1)
        var end = a.copy() if _length_sign(length_difference(a, b), lower, upper) < 0 else b^
        var start = minus_z^ if _length_sign(minus_z, lower, upper) > 0 else zero.copy()
        var overlap = length_difference(end, start)
        if _length_sign(overlap, lower, upper) != 1:
            raise Error("retained state has no positive physical overlap")
        mass.append(overlap^)
    # All orbits have size two, so the common factor cancels. M^2 acts
    # on endpoint vectors as beta^2 acts on the corresponding lengths.
    var square = new_matrix_power(2)
    var deficit = List[List[Int]]()
    for vector in mass:
        var budget = List[Int]()
        for k in range(3):
            var value = 0
            for j in range(3):
                value = checked_add(value, checked_mul(square.at(k, j), vector[j]))
            budget.append(value)
        deficit.append(budget^)
    for i in range(len(graph.rows)):
        for j in graph.rows[i]:
            for k in range(3):
                deficit[j][k] = checked_sub(deficit[j][k], mass[i][k])
    var losing = List[Bool]()
    for vector in deficit:
        var sign = _length_sign(vector, lower, upper)
        if sign < 0:
            raise Error("negative transpose mass deficit")
        losing.append(sign > 0)
    var witnesses = source_loss_witnesses(graph.rows, losing, 3)
    return (mass^, deficit^, witnesses^)
