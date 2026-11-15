"""SCC polynomial exclusions, authenticated spectral vectors and zero closure."""

from std.testing import assert_equal, assert_false, assert_true
from finite_exact.rat_q import Q
from finite_linear_algebra.scalar import q_int
from mojo_smoke.claims import require_contract
from psc.c4_nonunit_residue_occupancy import same_vector
from psc.c4_pair_overlap_new_incidence import build_new_incidence_graph, new_matrix_power
from psc.c4_overlap_scc_obstruction import (
    PositiveSpectralWitness, SccObstructionReport, analyze_overlap_system,
    analyze_new_source_scc, authenticate_new_scc_report, authenticate_overlap_partition,
    authenticate_overlap_scale, canonical_overlap_partition, certify_new_source_scc,
    classify_positive_witness, critical_spectral_witness, declared_roots_zero,
    make_overlap_scale, modular_component_attempt, rational_spectral_witness,
)


def rows_from_matrix(matrix: List[List[Int]]) raises -> List[List[Int]]:
    var rows = List[List[Int]]()
    for i in range(len(matrix)):
        if len(matrix[i]) != len(matrix):
            raise Error("control matrix must be square")
        var row = List[Int]()
        for j in range(len(matrix)):
            if matrix[i][j] < 0 or matrix[i][j] > 81:
                raise Error("control entry outside bounded nonnegative domain")
            for _ in range(matrix[i][j]):
                row.append(j)
        rows.append(row^)
    return rows^


def assert_vertex_zero_pattern(report: SccObstructionReport, pattern: List[Bool]) raises:
    assert_equal(len(pattern),len(report.partition.component_of))
    for i in range(len(pattern)):
        assert_equal(report.zero[report.partition.component_of[i]],pattern[i])


def positive_constant(component: Int) -> PositiveSpectralWitness:
    var coefficients = List[List[Q]]()
    coefficients.append([Q.one()])
    return critical_spectral_witness(component,coefficients)


def new_perron_vector() -> List[List[Q]]:
    # beta=(theta^2-4 theta-2)/5; F=(beta+1,theta,beta).
    var coefficients = List[List[Q]]()
    coefficients.append([Q(3,5),Q(-4,5),Q(1,5)])
    coefficients.append([Q.zero(),Q.one()])
    coefficients.append([Q(-2,5),Q(-4,5),Q(1,5)])
    return coefficients^


def test_canonical_components_and_preserved_multiplicity() raises:
    var rows: List[List[Int]] = [[1,1],[0,2],[2,2],[]]
    var partition = canonical_overlap_partition(rows)
    assert_equal(len(partition.members),3)
    assert_true(same_vector(partition.members[0],[0,1]))
    assert_true(same_vector(partition.members[1],[2]))
    assert_true(same_vector(partition.members[2],[3]))
    assert_true(same_vector(partition.outgoing[0],[1]))
    assert_true(same_vector(partition.incoming[1],[0]))
    authenticate_overlap_partition(rows,partition)
    var two = make_overlap_scale(0)
    var original: List[List[Int]] = [[0,0]]
    var original_partition = canonical_overlap_partition(original)
    var original_attempt = modular_component_attempt[101](original,original_partition,0,two)
    assert_equal(original_attempt.rank,0)
    var deduplicated: List[List[Int]] = [[0]]
    var changed_partition = canonical_overlap_partition(deduplicated)
    var changed_attempt = modular_component_attempt[101](deduplicated,changed_partition,0,two)
    assert_equal(changed_attempt.rank,1)
    assert_equal(changed_attempt.determinant,100)
    var refused = False
    partition.members[0][0] = 1
    try:
        authenticate_overlap_partition(rows,partition)
    except:
        refused = True
    assert_true(refused)


def test_noncritical_forcing_and_verified_subcritical_vector() raises:
    var rows = rows_from_matrix([[1,1],[0,2]])
    var witnesses = List[PositiveSpectralWitness]()
    witnesses.append(rational_spectral_witness(0,[1],1,1))
    witnesses.append(positive_constant(1))
    var report = analyze_overlap_system(rows,[0,1],make_overlap_scale(0),witnesses)
    assert_true(same_vector(report.spectral,[1,2]))
    assert_equal(report.exclusion[0],2)
    assert_equal(report.exclusion[1],0)
    assert_vertex_zero_pattern(report,[False,False])
    assert_false(declared_roots_zero(report))
    # The exact ray(1,1) solves this system. Noncritical does not mean zero.
    assert_equal(len(rows[0]),2)
    assert_equal(len(rows[1]),2)


def test_supercritical_ancestor_and_signed_algebraic_eigenvector() raises:
    var two = make_overlap_scale(0)
    var rows = rows_from_matrix([[3,1],[0,2]])
    var witnesses = List[PositiveSpectralWitness]()
    witnesses.append(rational_spectral_witness(0,[1],3,1))
    witnesses.append(positive_constant(1))
    var report = analyze_overlap_system(rows,[0,1],two,witnesses)
    assert_true(same_vector(report.spectral,[3,2]))
    assert_vertex_zero_pattern(report,[True,True])
    assert_true(declared_roots_zero(report))
    rows = rows_from_matrix([[3,1],[1,3]])
    var unresolved = analyze_overlap_system(rows,[0,1],two,List[PositiveSpectralWitness]())
    assert_equal(unresolved.exclusion[0],0)
    assert_false(declared_roots_zero(unresolved))
    for attempt in unresolved.attempts[0]:
        assert_equal(attempt.rank,1)
        assert_equal(attempt.determinant,0)
    witnesses = List[PositiveSpectralWitness]()
    witnesses.append(rational_spectral_witness(0,[1,1],4,1))
    report = analyze_overlap_system(rows,[0,1],two,witnesses)
    assert_equal(report.spectral[0],3)
    assert_vertex_zero_pattern(report,[True,True])
    var signed_coefficients: List[List[Q]] = [[Q.one()],[q_int(-1)]]
    var refused = False
    try:
        _ = classify_positive_witness(rows,canonical_overlap_partition(rows),two,critical_spectral_witness(0,signed_coefficients))
    except:
        refused = True
    assert_true(refused)


def test_critical_ancestor_descendants_and_incoming_equations() raises:
    var two = make_overlap_scale(0)
    var rows = rows_from_matrix([[2,1],[0,2]])
    var witnesses = List[PositiveSpectralWitness]()
    witnesses.append(positive_constant(0))
    witnesses.append(positive_constant(1))
    var report = analyze_overlap_system(rows,[0,1],two,witnesses)
    assert_vertex_zero_pattern(report,[False,True])
    # Restricting to the second root without keeping its incoming equations
    # enlarges the feasible cone. The full system certifies that root zero.
    var full = analyze_overlap_system(rows,[1],two,witnesses)
    assert_true(declared_roots_zero(full))
    var restricted_rows: List[List[Int]] = [[0,0]]
    var restricted_witnesses = List[PositiveSpectralWitness]()
    restricted_witnesses.append(positive_constant(0))
    var restricted = analyze_overlap_system(restricted_rows,[0],two,restricted_witnesses)
    assert_false(declared_roots_zero(restricted))
    # A critical block may point to a ZERO supercritical block and remain
    # algebraically allowed; outgoing edges do not themselves kill it.
    rows = rows_from_matrix([[2,1],[0,3]])
    witnesses = List[PositiveSpectralWitness]()
    witnesses.append(positive_constant(0))
    witnesses.append(rational_spectral_witness(1,[1],3,1))
    report = analyze_overlap_system(rows,[0,1],two,witnesses)
    assert_vertex_zero_pattern(report,[False,True])


def test_new_scale_critical_vector_and_nonperron_theta_factor() raises:
    var spectral_scale = make_overlap_scale()
    var square = new_matrix_power(2)
    var matrix = List[List[Int]]()
    for i in range(3):
        matrix.append([square.at(i,0),square.at(i,1),square.at(i,2)])
    var rows = rows_from_matrix(matrix)
    var witnesses = List[PositiveSpectralWitness]()
    witnesses.append(critical_spectral_witness(0,new_perron_vector()))
    var report = analyze_overlap_system(rows,[0,1,2],spectral_scale,witnesses)
    assert_equal(report.spectral[0],2)
    assert_vertex_zero_pattern(report,[False,False,False])
    for attempt in report.attempts[0]:
        assert_equal(attempt.rank,0)
    # [[D+I,I],[I,D+I]] has theta on(F,-F) but PF radius theta+2.
    var doubled = List[List[Int]]()
    for i in range(6):
        var row = List[Int]()
        for j in range(6):
            var entry = 0
            if i//3 == j//3:
                entry = square.at(i%3,j%3)+(1 if i == j else 0)
            elif i%3 == j%3:
                entry = 1
            row.append(entry)
        doubled.append(row^)
    rows = rows_from_matrix(doubled)
    witnesses = List[PositiveSpectralWitness]()
    witnesses.append(rational_spectral_witness(0,[4,7,3,4,7,3],8,1))
    report = analyze_overlap_system(rows,[0],spectral_scale,witnesses)
    assert_equal(report.spectral[0],3)
    assert_equal(report.exclusion[0],0)
    for attempt in report.attempts[0]:
        assert_true(attempt.rank < 6)
    assert_vertex_zero_pattern(report,[True,True,True,True,True,True])


def test_bad_prime_scale_and_spectral_witness_refusals() raises:
    var spectral_scale = make_overlap_scale()
    var rows: List[List[Int]] = [[0]]
    var partition = canonical_overlap_partition(rows)
    var bad_prime = modular_component_attempt[5](rows,partition,0,spectral_scale)
    var good_prime = modular_component_attempt[101](rows,partition,0,spectral_scale)
    assert_equal(bad_prime.rank,0)
    assert_equal(bad_prime.determinant,0)
    assert_equal(good_prime.rank,1)
    assert_equal(good_prime.determinant,96)
    var corrupted = spectral_scale.copy()
    corrupted.polynomial[0] = -3
    var refused = False
    try:
        authenticate_overlap_scale(corrupted)
    except:
        refused = True
    assert_true(refused)
    corrupted = spectral_scale.copy()
    corrupted.lo = q_int(0)
    refused = False
    try:
        authenticate_overlap_scale(corrupted)
    except:
        refused = True
    assert_true(refused)
    var two = make_overlap_scale(0)
    var critical_rows: List[List[Int]] = [[0,0]]
    for weight in [0,-1,1000001]:
        refused = False
        try:
            _ = classify_positive_witness(critical_rows,canonical_overlap_partition(critical_rows),two,rational_spectral_witness(0,[weight],2,1))
        except:
            refused = True
        assert_true(refused)
    for numerator in [0,1,3]:
        refused = False
        try:
            _ = classify_positive_witness(critical_rows,canonical_overlap_partition(critical_rows),two,rational_spectral_witness(0,[1],numerator,1))
        except:
            refused = True
        assert_true(refused)
    var false_positive: List[List[Q]] = [[Q.one()],[Q.one()]]
    var signed_rows = rows_from_matrix([[3,1],[1,3]])
    refused = False
    try:
        _ = classify_positive_witness(signed_rows,canonical_overlap_partition(signed_rows),two,critical_spectral_witness(0,false_positive))
    except:
        refused = True
    assert_true(refused)


def test_all_twelve_weight_free_modular_certificates() raises:
    var expected_counts: List[Int] = [3518,3259,3518,3031,3564,3516,3057,3525,3492,3554,3256,3503]
    var expected_largest: List[Int] = [143,391,123,622,56,119,622,123,119,56,391,143]
    var total_components = 0
    var total_degree = 0
    var total_modular = 0
    var total_states = 0
    for source in range(12):
        var report = certify_new_source_scc(source)
        assert_true(declared_roots_zero(report))
        assert_equal(len(report.partition.members),expected_counts[source])
        var largest = 0
        for c in range(len(report.partition.members)):
            var size = len(report.partition.members[c])
            if size > largest:
                largest = size
            total_components += 1
            total_states += size
            assert_true(report.zero[c])
            assert_false(report.budget_refused[c])
            assert_equal(report.spectral[c],0)  # No global or local weights.
            if report.exclusion[c] == 1:
                total_degree += 1
                assert_equal(size,1)
                assert_equal(len(report.attempts[c]),0)
            else:
                total_modular += 1
                assert_equal(report.exclusion[c],2)
                assert_equal(len(report.attempts[c]),1)
                assert_equal(report.attempts[c][0].prime,101)
                assert_equal(report.attempts[c][0].rank,size)
                assert_true(report.attempts[c][0].determinant != 0)
        assert_equal(largest,expected_largest[source])
    assert_equal(total_components,40793)
    assert_equal(total_degree,40765)
    assert_equal(total_modular,28)
    assert_equal(total_states,43915)


def test_submitted_report_graph_mutations_and_caps() raises:
    var graph = build_new_incidence_graph(0)
    var report = analyze_overlap_system(graph.rows,[0,1,2],make_overlap_scale(),List[PositiveSpectralWitness]())
    authenticate_new_scc_report(graph,report)
    var modular_component = -1
    for c in range(len(report.attempts)):
        if len(report.attempts[c]) > 0:
            modular_component = c
            break
    assert_true(modular_component >= 0)
    for mutation in range(5):
        var wrong = report.copy()
        if mutation == 0:
            wrong.zero[0] = False
        elif mutation == 1:
            wrong.attempts[modular_component][0].prime = 103
        elif mutation == 2:
            wrong.attempts[modular_component][0].rank -= 1
        elif mutation == 3:
            wrong.attempts[modular_component][0].determinant = 0
        else:
            wrong.partition.members[0][0] = 1
        var refused = False
        try:
            authenticate_new_scc_report(graph,wrong)
        except:
            refused = True
        assert_true(refused)
    var forged = graph.copy()
    var victim = -1
    for i in range(len(forged.rows)):
        if victim >= 0:
            break
        for a in range(len(forged.rows[i])):
            for b in range(a+1,len(forged.rows[i])):
                if forged.rows[i][a] == forged.rows[i][b]:
                    victim = i
    assert_true(victim >= 0)
    _ = forged.rows[victim].pop()
    var refused = False
    try:
        authenticate_new_scc_report(forged,report)
    except:
        refused = True
    assert_true(refused)
    var capped = analyze_new_source_scc(0,4)
    assert_false(declared_roots_zero(capped))
    var refused_count = 0
    for value in capped.budget_refused:
        if value:
            refused_count += 1
    assert_equal(refused_count,2)
    refused = False
    try:
        _ = certify_new_source_scc(0,4)
    except:
        refused = True
    assert_true(refused)
    var malformed_rows: List[List[List[Int]]] = [[[1]], [[-1]]]
    for invalid_rows in malformed_rows:
        refused = False
        try:
            _ = canonical_overlap_partition(invalid_rows)
        except:
            refused = True
        assert_true(refused)
    for budget in [0,769]:
        refused = False
        try:
            _ = analyze_overlap_system([[0]],[0],make_overlap_scale(),List[PositiveSpectralWitness](),budget)
        except:
            refused = True
        assert_true(refused)


def main() raises:
    test_canonical_components_and_preserved_multiplicity()
    test_noncritical_forcing_and_verified_subcritical_vector()
    test_supercritical_ancestor_and_signed_algebraic_eigenvector()
    test_critical_ancestor_descendants_and_incoming_equations()
    test_new_scale_critical_vector_and_nonperron_theta_factor()
    test_bad_prime_scale_and_spectral_witness_refusals()
    test_all_twelve_weight_free_modular_certificates()
    test_submitted_report_graph_mutations_and_caps()
    print("[PASS] complete SCC polynomial exclusions, verified spectral witnesses, safe zero propagation and refusal controls")
    require_contract("Authenticated complete paired-overlap SCC partitions, all twelve new-source modular certificates without old weight inputs, positive spectral witness checks, incoming-equation preservation and bounded inconclusive refusals")
