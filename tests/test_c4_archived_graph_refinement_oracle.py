"""Independent source-bound finite refinement and adversarial controls."""
from dataclasses import replace
from copy import deepcopy
from pathlib import Path
import hashlib
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'oracles/python'))
import c4_archived_graph_refinement as refinement


@pytest.mark.parametrize('fixture', [0, 1])
def test_complete_original_source_rows_and_archived_digest(fixture):
    binding, weights, iterations, gap = refinement.reference(fixture)
    assert refinement.validate_binding(binding) is binding
    assert refinement.validate_contraction(binding, weights) == gap
    assert len(binding.states) == (7150, 7083)[fixture]
    assert sum(map(len, binding.rows)) == (34826, 34853)[fixture]
    assert refinement.check_ordered_lift(binding) == 2*sum(map(len, binding.rows))
    assert len(binding.digits) == 15
    for digit in binding.digits:
        assert binding.images[binding.images[digit.parent][digit.outer]][digit.local] == digit.selected
        assert binding.words[digit.parent][digit.position] == digit.selected
    legacy = refinement.archive.graph_text(refinement.as_graph(binding), weights, iterations)
    assert hashlib.sha256(legacy.encode()).hexdigest() == (
        '23f85af92c327a64f70983db990753a84cd1489e3c72c3047e51f14e97afce6e',
        'a63d544b25b5f7146abbd25f1960fed77f85584a1f20957b5869bea30b389256',
    )[fixture]


@pytest.mark.parametrize('fixture', [0, 1])
def test_structural_mutations_fail_even_when_numeric_certificate_survives(fixture):
    observed = refinement.negative_controls(fixture)
    assert len(observed) == 15
    assert all(v['rejected'] for v in observed.values())
    assert observed['omitted_repeated_positional_edge']['numeric_subinvariance_still_valid']
    assert observed['flipped_track_swap']['numeric_subinvariance_still_valid']
    assert observed['incomplete_inverse_ancestry']['numeric_subinvariance_still_valid']


@pytest.mark.parametrize('fixture', [0, 1])
def test_removing_a_state_and_all_its_stored_edges_still_fails_completeness(fixture):
    binding, _, _, _ = refinement.reference(fixture)
    graph = refinement.as_graph(binding)
    graph.states.pop()
    graph.rows.pop()
    graph.rows = [[target for target in row if target < len(graph.states)] for row in graph.rows]
    with pytest.raises(refinement.InvalidCertificate, match='admitted integral inverse ancestor missing'):
        refinement.bind_graph(graph)


def test_exact_residue_and_strict_box_exclusion_boundaries():
    # M²*e0=(1,1,1) is an integral image despite its odd coordinates.
    assert refinement.integral_ancestor((1, 1, 1)) == (1, 0, 0)
    assert refinement.integral_ancestor((0, 0, 1)) is None
    assert refinement.integral_ancestor((2, 0, 0)) == (0, 1, -1)
    assert not refinement.outside_box((32, 0, 16))
    assert not refinement.outside_box((-32, 0, -16))
    assert refinement.outside_box((33, 0, 0))
    assert refinement.outside_box((0, 0, 17))


def test_complete_native_packet_and_omission_controls():
    lines = ['schema '+refinement.SCHEMA]
    for fixture in range(2):
        lines.extend(refinement.graph_lines(*refinement.reference(fixture)))
    packet = '\n'.join(lines)+'\n'
    assert refinement.verify_native(packet) == refinement.receipt()
    for mutated in ('\n'.join(lines[:-1]), '\n'.join(lines+[lines[-1]]),
                    packet.replace('graph 0 2 16 8 0 ', 'graph 0 2 24 12 0 ', 1)):
        with pytest.raises(refinement.InvalidCertificate):
            refinement.verify_native(mutated)
    # Reference-generated packet is calibration.  Only an actual supplied
    # native file is counted as cross-language replay.
    native = os.environ.get('PSC_ARCHIVED_GRAPH_REFINEMENT_NATIVE_OUTPUT')
    if native:
        assert refinement.verify_native(Path(native).read_text()) == refinement.receipt()


def test_python_optimization_cannot_bypass_refinement_admission():
    script = (
        f'import sys; sys.path.insert(0, {str(ROOT/"oracles/python")!r}); '
        'import c4_archived_graph_refinement as r; '
        "r.verify_native('schema '+r.SCHEMA+'\\n'); print('CERTIFIED')"
    )
    result = subprocess.run([sys.executable, '-O', '-c', script], capture_output=True, text=True)
    assert result.returncode != 0
    assert not result.stdout
    assert 'mismatch' in result.stderr
