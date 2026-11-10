"""Complete strict-system Parikh/flat-hub conformance audit.

Every child is a real ordered balanced factor: build_derived_system
reconstructs the entire source-word factorization before the audit runs.
This reports necessary algebraic constraints of a GIVEN fully strict
system. Candidate good edges are not certified eventually coincident.

For irreducible ternary incidence, rank three in each depth<=2 cone follows
from the cyclic-vector argument of c4_two_generation_rank. This checker
never infers C4, finite-G1, or irreducible Pisot from a finite graph.
"""

from psc.bpa import substitution_incidence, prefix_endpoint_map
from psc.derived_system import build_derived_system
from psc.good_edge_system import candidate_good_edge_mask
from psc.hub_cocycle import build_hub_cocycle
from psc.c4_two_generation_rank import _cross_nonzero, _rank_det
from psc.words import Pair, parikh


struct ConePivot(Copyable, Movable):
    var root: Int
    var depth: Int
    var first_ordinal: Int
    var second_ordinal: Int
    var state_id: Int
    var counts: List[Int]

    def __init__(
        out self, root: Int, depth: Int, first_ordinal: Int,
        second_ordinal: Int, state_id: Int, counts: List[Int],
    ):
        self.root = root
        self.depth = depth
        self.first_ordinal = first_ordinal
        self.second_ordinal = second_ordinal
        self.state_id = state_id
        self.counts = counts.copy()


struct StrictConeHubAudit(Copyable, Movable):
    var candidate_good_mask: Int
    var flat_candidate_good_mask: Int
    var global_rank: Int
    var root_ranks: List[Int]
    var root_pivots: List[List[ConePivot]]
    var plane_normal: List[Int]
    var plane_eigenvalue: Int

    def __init__(
        out self, candidate_good_mask: Int, flat_candidate_good_mask: Int,
        global_rank: Int, root_ranks: List[Int],
        root_pivots: List[List[ConePivot]], plane_normal: List[Int],
        plane_eigenvalue: Int,
    ):
        self.candidate_good_mask = candidate_good_mask
        self.flat_candidate_good_mask = flat_candidate_good_mask
        self.global_rank = global_rank
        self.root_ranks = root_ranks.copy()
        self.root_pivots = root_pivots.copy()
        self.plane_normal = plane_normal.copy()
        self.plane_eigenvalue = plane_eigenvalue


def _consider(mut pivots: List[ConePivot], candidate: ConePivot) raises:
    if len(pivots) == 0:
        if candidate.counts[0] != 0 or candidate.counts[1] != 0 or candidate.counts[2] != 0:
            pivots.append(candidate.copy())
    elif len(pivots) == 1:
        if _cross_nonzero(pivots[0].counts, candidate.counts):
            pivots.append(candidate.copy())
    elif len(pivots) == 2:
        if _rank_det(
            pivots[0].counts, pivots[1].counts, candidate.counts
        ) != 0:
            pivots.append(candidate.copy())


def _gcd(a: Int, b: Int) -> Int:
    var x = abs(a)
    var y = abs(b)
    while y != 0:
        var old = x % y
        x = y
        y = old
    return x


def _plane_normal_and_eigenvalue(
    masses: List[List[Int]], m: List[Int],
    global_pivots: List[ConePivot],
) raises -> List[Int]:
    """Return primitive normal and integral left eigenvalue, for rank two.

    A fully child-closed system makes im(P) M-invariant by literal
    Parikh conservation. At rank 2 its annihilator is one-dimensional,
    so the primitive normal is an integral LEFT eigenvector of M.
    """
    if len(global_pivots) != 2 or len(m) != 9:
        raise Error("codimension-one obstruction requires global rank two")
    ref a = global_pivots[0].counts
    ref b = global_pivots[1].counts
    var n: List[Int] = [
        a[1] * b[2] - a[2] * b[1],
        a[2] * b[0] - a[0] * b[2],
        a[0] * b[1] - a[1] * b[0],
    ]
    var divisor = _gcd(n[0], _gcd(n[1], n[2]))
    if divisor == 0:
        raise Error("rank two has no nonzero annihilator")
    for i in range(3):
        n[i] //= divisor
    for i in range(3):
        if n[i] != 0:
            if n[i] < 0:
                for j in range(3):
                    n[j] = -n[j]
            break
    for j in range(len(masses)):
        var dot = 0
        for i in range(3):
            dot += n[i] * masses[j][i]
        if dot != 0:
            raise Error("global Parikh normal does not annihilate every state")
    var lambda_value = 0
    var found = False
    for col in range(3):
        var val = 0
        for i in range(3):
            val += n[i] * m[3 * i + col]
        if n[col] != 0 and not found:
            if val % n[col] != 0:
                raise Error("integral incidence has nonintegral rational eigenvalue")
            lambda_value = val // n[col]
            found = True
        if n[col] == 0 and val != 0:
            raise Error("rank-two annihilator is not M-invariant")
    if not found:
        raise Error("empty plane normal")
    for col in range(3):
        var val = 0
        for i in range(3):
            val += n[i] * m[3 * i + col]
        if val != lambda_value * n[col]:
            raise Error("normal does not define an exact left eigenvector")
    n.append(lambda_value)
    return n^


def audit_complete_strict_cones(
    sigma: List[List[Int]], states: List[Pair],
    occurrence_cap: Int = 50000,
) raises -> StrictConeHubAudit:
    """Audit ALL source roots to depth two; refuse truncated graph/caps.

    Every source state is bounded to 256 letters, every image to 16,
    so every level-two occurrence column has <=65536 coordinates and
    all 3x3 minors fit signed 64-bit Int. Limits restrict *this
    executable*, not the mathematical rank theorem.
    """
    if occurrence_cap <= 0 or len(states) == 0 or len(states) > 2000:
        raise Error("invalid strict cone audit budget")
    if len(sigma) != 3:
        raise Error("strict cone audit is ternary")
    for a in range(3):
        if len(sigma[a]) == 0 or len(sigma[a]) > 16:
            raise Error("substitution image outside strict cone arithmetic budget")
        for j in range(len(sigma[a])):
            if sigma[a][j] < 0 or sigma[a][j] >= 3:
                raise Error("substitution image contains invalid letter")
    for j in range(len(states)):
        if states[j].length() <= 0 or states[j].length() > 256:
            raise Error("strict cone parent outside checked arithmetic budget")

    var ds = build_derived_system(sigma, states)
    var m = substitution_incidence(sigma)
    var masses = List[List[Int]]()
    for i in range(ds.size()):
        masses.append(parikh(ds.states[i].u))
    # Per-state FULL literal one-step Parikh conservation.
    for src in range(ds.size()):
        for row in range(3):
            var total = 0
            for j in range(len(ds.images[src])):
                total += masses[ds.images[src][j]][row]
            var expected = 0
            for a in range(3):
                expected += m[3 * row + a] * masses[src][a]
            if total != expected:
                raise Error("child-occurrence Parikh sum mismatches literal inflation")

    var global_pivots = List[ConePivot]()
    for i in range(ds.size()):
        _consider(global_pivots, ConePivot(i, 0, -1, -1, i, masses[i]))
    var ranks = List[Int]()
    var paths = List[List[ConePivot]]()
    for root in range(ds.size()):
        var pivots = List[ConePivot]()
        var seen = 0
        _consider(pivots, ConePivot(root, 0, -1, -1, root, masses[root]))
        seen += 1
        for j in range(len(ds.images[root])):
            if seen >= occurrence_cap:
                raise Error("two-generation strict cone enumeration capped")
            var child = ds.images[root][j]
            _consider(pivots, ConePivot(root, 1, j, -1, child, masses[child]))
            seen += 1
        for j in range(len(ds.images[root])):
            var child = ds.images[root][j]
            for k in range(len(ds.images[child])):
                if seen >= occurrence_cap:
                    raise Error("two-generation strict cone enumeration capped")
                var grandchild = ds.images[child][k]
                _consider(pivots, ConePivot(root, 2, j, k, grandchild, masses[grandchild]))
                seen += 1
        ranks.append(len(pivots))
        paths.append(pivots^)

    # A compatible candidate is NOT certified to be BD-good. Only
    # genuine eventually-coincident good edges permit a C4 inference.
    var mask = candidate_good_edge_mask(ds, prefix_endpoint_map(sigma))
    var flat = 0
    for edge in range(3):
        if (mask & (1 << edge)) == 0:
            continue
        var hub = 0
        if edge == 0:
            hub = 2
        elif edge == 1:
            hub = 1
        var cocycle = build_hub_cocycle(ds, hub)
        var all_zero = True
        for src in range(ds.size()):
            for j in range(len(ds.images[src])):
                if cocycle.residual_bits[src][j] != 0:
                    all_zero = False
        if all_zero:
            flat |= 1 << edge

    var normal = List[Int]()
    var eigenvalue = 0
    if len(global_pivots) == 2:
        var certificate = _plane_normal_and_eigenvalue(masses, m, global_pivots)
        for i in range(3):
            normal.append(certificate[i])
        eigenvalue = certificate[3]
    return StrictConeHubAudit(mask, flat, len(global_pivots), ranks, paths, normal, eigenvalue)
