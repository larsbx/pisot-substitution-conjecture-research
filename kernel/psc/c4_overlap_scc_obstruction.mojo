"""Authenticated SCC obstruction certificates for complete paired overlaps.

Literature GO: docs/c4-critical-overlap-components-literature-gate-2026-11-05.md.
Rows point from a parent to every actual child occurrence. Repeated targets
are retained. Finite linear feasibility does not assert geometric positivity.
"""

from finite_graph.scc import sccs
from finite_exact.checked_int import checked_add, checked_mul
from finite_exact.fp import Fp
from finite_exact.rat_q import Q
from finite_linear_algebra.qpoly import add, mul, remainder, scale, sub
from finite_linear_algebra.scalar import q_int
from psc.exact import q_poly, require_q
from psc.pisot import is_irreducible_cubic
from psc.real_root_sign import count_real_roots, sign_at_isolated_root
from psc.c4_nonunit_residue_occupancy import same_vector
from psc.c4_pair_overlap_new_incidence import (
    NewIncidenceGraph, authenticate_new_graph, build_new_incidence_graph,
    make_new_chart, new_matrix_power,
)

comptime SCC_BLOCK_BUDGET = 768
comptime SCC_GRAPH_BUDGET = 20000
comptime SCC_CONDENSATION_SCAN_BUDGET = 20000000


struct OverlapScale(Copyable, Movable):
    """Only the authenticated rational two or new-incidence beta-squared."""
    var kind: Int
    var polynomial: List[Int]
    var lo: Q
    var hi: Q

    def __init__(out self, kind: Int, polynomial: List[Int], lo: Q, hi: Q):
        self.kind = kind
        self.polynomial = polynomial.copy()
        self.lo = lo.copy()
        self.hi = hi.copy()


struct ModularAttempt(Copyable, Movable):
    var prime: Int
    var rank: Int
    var determinant: Int

    def __init__(out self, prime: Int, rank: Int, determinant: Int):
        self.prime = prime
        self.rank = rank
        self.determinant = determinant


struct PositiveSpectralWitness(Copyable, Movable):
    """A proposed vector and mechanism, never an accepted spectral label.

    kind1 is a rational Collatz vector with a rational rate; its verified
    comparison with theta determines subcritical, critical or supercritical.
    kind2 proposes a positive polynomial-field theta eigenvector.
    """
    var component: Int
    var kind: Int
    var weights: List[Int]
    var coefficients: List[List[Q]]
    var numerator: Int
    var denominator: Int

    def __init__(out self, component: Int, kind: Int, weights: List[Int], coefficients: List[List[Q]], numerator: Int, denominator: Int):
        self.component = component
        self.kind = kind
        self.weights = weights.copy()
        self.coefficients = coefficients.copy()
        self.numerator = numerator
        self.denominator = denominator


struct OverlapPartition(Copyable, Movable):
    var members: List[List[Int]]
    var component_of: List[Int]
    var local_index: List[Int]
    var outgoing: List[List[Int]]
    var incoming: List[List[Int]]

    def __init__(out self, members: List[List[Int]], component_of: List[Int], local_index: List[Int], outgoing: List[List[Int]], incoming: List[List[Int]]):
        self.members = members.copy()
        self.component_of = component_of.copy()
        self.local_index = local_index.copy()
        self.outgoing = outgoing.copy()
        self.incoming = incoming.copy()


def validate_overlap_rows(rows: List[List[Int]]) raises:
    if len(rows) < 1 or len(rows) > SCC_GRAPH_BUDGET:
        raise Error("overlap system dimension outside explicit 1..20000 budget; inconclusive")
    for row in rows:
        if len(row) > 81:
            raise Error("overlap row outside explicit 81-occurrence budget")
        for target in row:
            if target < 0 or target >= len(rows):
                raise Error("overlap target outside authenticated state inventory")


def canonical_overlap_partition(rows: List[List[Int]]) raises -> OverlapPartition:
    """Recompute SCCs; ascending members and ascending minimum-vertex IDs."""
    validate_overlap_rows(rows)
    var raw = sccs(rows)
    var raw_of = List[Int](length=len(rows),fill=-1)
    for c in range(len(raw)):
        if len(raw[c]) < 1:
            raise Error("empty SCC from canonical decomposition")
        for vertex in raw[c]:
            if vertex < 0 or vertex >= len(rows) or raw_of[vertex] != -1:
                raise Error("invalid SCC partition from canonical decomposition")
            raw_of[vertex] = c
    var rename = List[Int](length=len(raw),fill=-1)
    var members = List[List[Int]]()
    var component_of = List[Int](length=len(rows),fill=-1)
    var local_index = List[Int](length=len(rows),fill=-1)
    for vertex in range(len(rows)):
        if raw_of[vertex] < 0:
            raise Error("canonical SCC partition omitted a vertex")
        var old = raw_of[vertex]
        if rename[old] < 0:
            rename[old] = len(members)
            members.append(List[Int]())
        var c = rename[old]
        component_of[vertex] = c
        local_index[vertex] = len(members[c])
        members[c].append(vertex)
    var outgoing = List[List[Int]]()
    var incoming = List[List[Int]]()
    if checked_mul(len(members),len(members)) > SCC_CONDENSATION_SCAN_BUDGET:
        raise Error("condensation normalization scan budget exceeded; inconclusive")
    for _ in range(len(members)):
        outgoing.append(List[Int]())
        incoming.append(List[Int]())
    var marked = List[Int](length=len(members),fill=-1)
    for c in range(len(members)):
        for vertex in members[c]:
            for target in rows[vertex]:
                var other = component_of[target]
                if other != c:
                    marked[other] = c
        for other in range(len(members)):
            if marked[other] == c:
                outgoing[c].append(other)
                incoming[other].append(c)
    return OverlapPartition(members,component_of,local_index,outgoing,incoming)


def _same_rows(a: List[List[Int]], b: List[List[Int]]) -> Bool:
    if len(a) != len(b):
        return False
    for i in range(len(a)):
        if not same_vector(a[i],b[i]):
            return False
    return True


def authenticate_overlap_partition(rows: List[List[Int]], supplied: OverlapPartition) raises:
    var expected = canonical_overlap_partition(rows)
    if not _same_rows(supplied.members,expected.members) or not same_vector(supplied.component_of,expected.component_of) or not same_vector(supplied.local_index,expected.local_index) or not _same_rows(supplied.outgoing,expected.outgoing) or not _same_rows(supplied.incoming,expected.incoming):
        raise Error("SCC partition differs from complete canonical decomposition")


def make_overlap_scale(kind: Int = 1) raises -> OverlapScale:
    if kind == 0:
        # The interval is open and isolates the exact root2 of x-2.
        var polynomial: List[Int] = [-2,1]
        var lo = Q(3,2)
        var hi = Q(5,2)
        if count_real_roots(q_poly(polynomial),lo,hi) != 1:
            raise Error("rational scale isolation failed")
        return OverlapScale(0,polynomial,lo,hi)
    if kind != 1:
        raise Error("unsupported overlap spectral scale")
    var polynomial: List[Int] = [-4,5,-7,1]
    if not same_vector(new_matrix_power(2).charpoly(),polynomial) or not is_irreducible_cubic(polynomial):
        raise Error("new beta-squared irreducible polynomial authentication failed")
    var x2 = q_poly([0,0,1])
    var composed = q_poly([1])
    for degree in range(2,-1,-1):
        composed = add(mul(composed,x2),q_poly([polynomial[degree]]))
    if len(remainder(composed,q_poly([-2,-3,-1,1]))) != 0:
        raise Error("new beta-squared polynomial does not annihilate beta squared")
    var lo = Q(63,10)
    var hi = Q(32,5)
    var chart = make_new_chart()
    var squared = chart.beta.square()
    if squared.rejected or not lo.lt(squared.lo) or not squared.hi.lt(hi):
        raise Error("new theta scale is not the authenticated beta square")
    if count_real_roots(q_poly(polynomial),lo,hi) != 1:
        raise Error("new theta interval does not isolate one root")
    return OverlapScale(1,polynomial,lo,hi)


def authenticate_overlap_scale(supplied: OverlapScale) raises:
    var expected = make_overlap_scale(supplied.kind)
    if not same_vector(supplied.polynomial,expected.polynomial) or supplied.lo.rejected or supplied.hi.rejected or not supplied.lo.eq(expected.lo) or not supplied.hi.eq(expected.hi):
        raise Error("overlap scale differs from its authenticated polynomial and isolation")


def rational_spectral_witness(component: Int, weights: List[Int], numerator: Int, denominator: Int) -> PositiveSpectralWitness:
    return PositiveSpectralWitness(component,1,weights,List[List[Q]](),numerator,denominator)


def critical_spectral_witness(component: Int, coefficients: List[List[Q]]) -> PositiveSpectralWitness:
    return PositiveSpectralWitness(component,2,List[Int](),coefficients,0,0)


def _sign_at_scale(spectral_scale: OverlapScale, value: List[Q]) raises -> Int:
    # Every entry point authenticates a one-root interval first.  The
    # vendored/PSC Tarski sign primitive does not prove isolation by itself.
    return sign_at_isolated_root(q_poly(spectral_scale.polynomial),value,spectral_scale.lo,spectral_scale.hi)


def _classify_positive_witness(rows: List[List[Int]], partition: OverlapPartition, spectral_scale: OverlapScale, witness: PositiveSpectralWitness) raises -> Int:
    var c = witness.component
    if c < 0 or c >= len(partition.members):
        raise Error("spectral witness component outside authenticated partition")
    var size = len(partition.members[c])
    if witness.kind == 1:
        if len(witness.weights) != size or len(witness.coefficients) != 0 or witness.numerator < 1 or witness.numerator > 10000 or witness.denominator < 1 or witness.denominator > 1000:
            raise Error("rational spectral witness shape or rate budget")
        for weight in witness.weights:
            if weight < 1 or weight > 1000000:
                raise Error("spectral witness requires positive bounded weights")
        var relation = List[Q]()
        relation.append(Q(Int64(witness.numerator),Int64(witness.denominator)))
        relation.append(q_int(-1))
        var sign = _sign_at_scale(spectral_scale,relation)
        for i in range(size):
            var total = 0
            for target in rows[partition.members[c][i]]:
                if partition.component_of[target] == c:
                    total = checked_add(total,witness.weights[partition.local_index[target]])
            var lhs = checked_mul(witness.denominator,total)
            var rhs = checked_mul(witness.numerator,witness.weights[i])
            if sign < 0 and lhs > rhs:
                raise Error("false positive subcritical witness")
            if sign > 0 and lhs < rhs:
                raise Error("false positive supercritical witness")
            if sign == 0 and lhs != rhs:
                raise Error("false exact rational critical witness")
        return 1 if sign < 0 else (3 if sign > 0 else 2)
    if witness.kind != 2 or len(witness.weights) != 0 or len(witness.coefficients) != size or witness.numerator != 0 or witness.denominator != 0:
        raise Error("polynomial-field spectral witness shape")
    var degree = len(spectral_scale.polynomial)-1
    for value in witness.coefficients:
        if len(value) < 1 or len(value) > degree:
            raise Error("critical vector is outside the canonical field-basis dimension")
        for coefficient in value:
            _ = require_q(coefficient,"critical field coefficient")
        if _sign_at_scale(spectral_scale,value) <= 0:
            raise Error("critical field vector must be strictly positive at theta")
    for i in range(size):
        var image = List[Q]()
        for target in rows[partition.members[c][i]]:
            if partition.component_of[target] == c:
                image = add(image,witness.coefficients[partition.local_index[target]])
        var equation = sub(image,mul(q_poly([0,1]),witness.coefficients[i]))
        if len(remainder(equation,q_poly(spectral_scale.polynomial))) != 0:
            raise Error("false polynomial-field theta eigenvector")
    return 2


def classify_positive_witness(rows: List[List[Int]], partition: OverlapPartition, spectral_scale: OverlapScale, witness: PositiveSpectralWitness) raises -> Int:
    authenticate_overlap_scale(spectral_scale)
    authenticate_overlap_partition(rows,partition)
    return _classify_positive_witness(rows,partition,spectral_scale,witness)


def _modular_attempt[p: Int64](rows: List[List[Int]], partition: OverlapPartition, component: Int, polynomial: List[Int], block_budget: Int) raises -> ModularAttempt:
    var size = len(partition.members[component])
    if size < 1 or size > block_budget or block_budget > SCC_BLOCK_BUDGET:
        raise Error("modular component dimension budget exceeded; inconclusive")
    var entries = checked_mul(size,size)
    var current = List[Fp[p]](length=entries,fill=Fp[p].zero())
    for i in range(size):
        current[size*i+i] = Fp[p](Int64(polynomial[len(polynomial)-1]))
    # Sparse Horner multiplication by the ACTUAL occurrence rows. Each
    # repeated edge adds the corresponding matrix row once more.
    for degree in range(len(polynomial)-2,-1,-1):
        var updated = List[Fp[p]](length=entries,fill=Fp[p].zero())
        for i in range(size):
            var vertex = partition.members[component][i]
            for target in rows[vertex]:
                if partition.component_of[target] == component:
                    var k = partition.local_index[target]
                    for j in range(size):
                        updated[size*i+j] = updated[size*i+j] + current[size*k+j]
            updated[size*i+i] = updated[size*i+i] + Fp[p](Int64(polynomial[degree]))
        current = updated^
    var rank = 0
    var determinant = Fp[p].one()
    for column in range(size):
        if rank == size:
            break
        var pivot_row = -1
        for row in range(rank,size):
            if not current[size*row+column].accepted():
                raise Error("rejected finite-field pivot candidate")
            if not current[size*row+column].is_zero():
                pivot_row = row
                break
        if pivot_row < 0:
            continue
        if pivot_row != rank:
            for j in range(size):
                current.swap_elements(size*rank+j,size*pivot_row+j)
            determinant = -determinant
        var pivot = current[size*rank+column].copy()
        var inverse = pivot.inverse()
        if not inverse.accepted():
            raise Error("rejected finite-field pivot inverse")
        determinant = determinant * pivot
        for j in range(column,size):
            current[size*rank+j] = current[size*rank+j] * inverse
        for row in range(rank+1,size):
            var factor = current[size*row+column].copy()
            if factor.is_zero():
                continue
            if not factor.accepted():
                raise Error("rejected finite-field elimination factor")
            for j in range(column,size):
                current[size*row+j] = current[size*row+j] - factor * current[size*rank+j]
        rank += 1
    if rank != size:
        determinant = Fp[p].zero()
    if not determinant.accepted():
        raise Error("rejected finite-field determinant")
    return ModularAttempt(Int(p),rank,Int(determinant.v))


def modular_component_attempt[p: Int64](rows: List[List[Int]], partition: OverlapPartition, component: Int, spectral_scale: OverlapScale, block_budget: Int = SCC_BLOCK_BUDGET) raises -> ModularAttempt:
    authenticate_overlap_scale(spectral_scale)
    authenticate_overlap_partition(rows,partition)
    if component < 0 or component >= len(partition.members) or block_budget < 1 or block_budget > SCC_BLOCK_BUDGET:
        raise Error("modular component or budget outside authenticated domain")
    return _modular_attempt[p](rows,partition,component,spectral_scale.polynomial,block_budget)


struct SccObstructionReport(Copyable, Movable):
    var partition: OverlapPartition
    var spectral_scale: OverlapScale
    var block_budget: Int
    var roots: List[Int]
    # exclusion:0 unresolved,1 irreducible-degree,2 modular full-rank.
    var exclusion: List[Int]
    # spectral:0 unclassified,1 verified subcritical,2 critical,3 supercritical.
    var spectral: List[Int]
    var zero: List[Bool]
    var budget_refused: List[Bool]
    var attempts: List[List[ModularAttempt]]

    def __init__(out self, partition: OverlapPartition, spectral_scale: OverlapScale, block_budget: Int, roots: List[Int], exclusion: List[Int], spectral: List[Int], zero: List[Bool], budget_refused: List[Bool], attempts: List[List[ModularAttempt]]):
        self.partition = partition.copy()
        self.spectral_scale = spectral_scale.copy()
        self.block_budget = block_budget
        self.roots = roots.copy()
        self.exclusion = exclusion.copy()
        self.spectral = spectral.copy()
        self.zero = zero.copy()
        self.budget_refused = budget_refused.copy()
        self.attempts = attempts.copy()


def _queue_zero(component: Int, mut zero: List[Bool], mut queue: List[Int]):
    if not zero[component]:
        zero[component] = True
        queue.append(component)


def _zero_closure(partition: OverlapPartition, exclusion: List[Int], spectral: List[Int]) raises -> List[Bool]:
    var count = len(partition.members)
    var zero = List[Bool](length=count,fill=False)
    var queue = List[Int]()
    var pending = List[Int]()
    for c in range(count):
        pending.append(len(partition.outgoing[c]))
        if spectral[c] == 3:
            _queue_zero(c,zero,queue)
        elif spectral[c] == 2:
            # A critical block forces only its STRICT descendants zero.
            for other in partition.outgoing[c]:
                _queue_zero(other,zero,queue)
    for c in range(count):
        var noncritical = exclusion[c] != 0 or spectral[c] == 1 or spectral[c] == 3
        if pending[c] == 0 and noncritical:
            _queue_zero(c,zero,queue)
    var cursor = 0
    while cursor < len(queue):
        var c = queue[cursor]
        cursor += 1
        # A zero row cannot point to any positive coordinate in Tv=theta*v.
        for other in partition.outgoing[c]:
            _queue_zero(other,zero,queue)
        for parent in partition.incoming[c]:
            pending[parent] -= 1
            if pending[parent] < 0:
                raise Error("duplicate or impossible condensation decrement")
            var noncritical = exclusion[parent] != 0 or spectral[parent] == 1 or spectral[parent] == 3
            if pending[parent] == 0 and noncritical:
                _queue_zero(parent,zero,queue)
    return zero^


def analyze_overlap_system(rows: List[List[Int]], roots: List[Int], spectral_scale: OverlapScale, witnesses: List[PositiveSpectralWitness], block_budget: Int = SCC_BLOCK_BUDGET) raises -> SccObstructionReport:
    validate_overlap_rows(rows)
    authenticate_overlap_scale(spectral_scale)
    if block_budget < 1 or block_budget > SCC_BLOCK_BUDGET:
        raise Error("SCC matrix budget outside supported 1..768")
    if len(roots) < 1:
        raise Error("overlap system must declare at least one root")
    var root_seen = List[Bool](length=len(rows),fill=False)
    for root in roots:
        if root < 0 or root >= len(rows):
            raise Error("overlap root outside state inventory")
        if root_seen[root]:
            raise Error("duplicate declared overlap root")
        root_seen[root] = True
    var partition = canonical_overlap_partition(rows)
    var count = len(partition.members)
    var spectral = List[Int](length=count,fill=0)
    for witness in witnesses:
        if witness.component < 0 or witness.component >= count:
            raise Error("spectral witness outside canonical partition")
        if spectral[witness.component] != 0:
            raise Error("duplicate spectral witness for a component")
        spectral[witness.component] = _classify_positive_witness(rows,partition,spectral_scale,witness)
    var exclusion = List[Int](length=count,fill=0)
    var refused = List[Bool](length=count,fill=False)
    var attempts = List[List[ModularAttempt]]()
    var degree = len(spectral_scale.polynomial)-1
    for c in range(count):
        attempts.append(List[ModularAttempt]())
        var size = len(partition.members[c])
        if size < degree:
            # Both supported scale polynomials are authenticated irreducible.
            exclusion[c] = 1
        elif size > block_budget:
            refused[c] = True
        else:
            var first = _modular_attempt[101](rows,partition,c,spectral_scale.polynomial,block_budget)
            attempts[c].append(first.copy())
            if first.rank == size:
                exclusion[c] = 2
            else:
                var second = _modular_attempt[103](rows,partition,c,spectral_scale.polynomial,block_budget)
                attempts[c].append(second.copy())
                if second.rank == size:
                    exclusion[c] = 2
                else:
                    var third = _modular_attempt[107](rows,partition,c,spectral_scale.polynomial,block_budget)
                    attempts[c].append(third.copy())
                    if third.rank == size:
                        exclusion[c] = 2
        if exclusion[c] != 0 and spectral[c] == 2:
            raise Error("inconsistent verified critical and eigenvalue-exclusion certificates")
    var zero = _zero_closure(partition,exclusion,spectral)
    return SccObstructionReport(partition,spectral_scale,block_budget,roots,exclusion,spectral,zero,refused,attempts)


def declared_roots_zero(report: SccObstructionReport) -> Bool:
    """Summary of a report; submitted reports need authentication separately."""
    for root in report.roots:
        if not report.zero[report.partition.component_of[root]]:
            return False
    return True


def analyze_new_source_scc(source: Int, block_budget: Int = SCC_BLOCK_BUDGET) raises -> SccObstructionReport:
    var graph = build_new_incidence_graph(source)
    return analyze_overlap_system(graph.rows,[0,1,2],make_overlap_scale(),List[PositiveSpectralWitness](),block_budget)


def certify_new_source_scc(source: Int, block_budget: Int = SCC_BLOCK_BUDGET) raises -> SccObstructionReport:
    var report = analyze_new_source_scc(source,block_budget)
    if not declared_roots_zero(report):
        raise Error("new source has unresolved root components; inconclusive")
    return report^


def authenticate_new_scc_report(graph: NewIncidenceGraph, supplied: SccObstructionReport) raises:
    authenticate_new_graph(graph)
    if graph.model.rx != 8 or graph.model.ry != 8:
        raise Error("new source SCC adapter is scoped to its authenticated Q8 model")
    var expected = analyze_overlap_system(graph.rows,[0,1,2],make_overlap_scale(),List[PositiveSpectralWitness](),supplied.block_budget)
    authenticate_overlap_partition(graph.rows,supplied.partition)
    authenticate_overlap_scale(supplied.spectral_scale)
    if supplied.spectral_scale.kind != 1 or not same_vector(supplied.roots,expected.roots) or not same_vector(supplied.exclusion,expected.exclusion) or not same_vector(supplied.spectral,expected.spectral):
        raise Error("source SCC report differs from reconstructed exclusion inventory")
    if len(supplied.zero) != len(expected.zero) or len(supplied.budget_refused) != len(expected.budget_refused) or len(supplied.attempts) != len(expected.attempts):
        raise Error("source SCC report dimensions differ")
    for c in range(len(expected.zero)):
        if supplied.zero[c] != expected.zero[c] or supplied.budget_refused[c] != expected.budget_refused[c] or len(supplied.attempts[c]) != len(expected.attempts[c]):
            raise Error("source SCC report has false zero/budget/attempt metadata")
        for j in range(len(expected.attempts[c])):
            var actual = supplied.attempts[c][j].copy()
            var desired = expected.attempts[c][j].copy()
            if actual.prime != desired.prime or actual.rank != desired.rank or actual.determinant != desired.determinant:
                raise Error("source SCC modular certificate differs from complete reconstruction")
