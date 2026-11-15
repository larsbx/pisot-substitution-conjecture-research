"""Independent original-payload reconstruction and adversarial import checks."""

from functools import lru_cache
from pathlib import Path
import os
import subprocess
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT/'oracles/python'))
import c4_archived_payload as payload
import c4_archived_graph_refinement as refinement


@lru_cache(maxsize=1)
def inputs():
    native = os.environ.get('PSC_ARCHIVED_PAYLOAD_NATIVE_OUTPUT')
    if native:
        text = Path(native).read_text()
        return text, payload.parse_payload(text)
    # Calibration is explicitly separate from an actual cross-language run.
    records = tuple(payload.calibration_payload(*refinement.reference(f)) for f in range(2))
    text = 'schema '+payload.SCHEMA+'\n'+''.join('\n'.join(payload.payload_lines(p))+'\n' for p in records)
    return text, records


@pytest.mark.parametrize('fixture', [0, 1])
def test_original_graph_fields_addresses_weights_and_lookup(fixture):
    _, records = inputs()
    record = records[fixture]
    result = payload.validate_payload(record)
    assert result['states'] == (7150, 7083)[fixture]
    assert result['positional_edges'] == (34826, 34853)[fixture]
    assert result['historical_graph_sha256'] == (
        '23f85af92c327a64f70983db990753a84cd1489e3c72c3047e51f14e97afce6e',
        'a63d544b25b5f7146abbd25f1960fed77f85584a1f20957b5869bea30b389256')[fixture]
    assert len(record.packed) == len(record.lookup) == result['states']
    assert len(record.binding.digits) == 15
    assert all(payload.orbit_key(state) == payload.orbit_key(refinement.swap(state))
               for state in record.binding.states)


def test_independent_exact_field_calibrations_keep_parallel_positions():
    state = (0, 1, 0, 0, 0)
    assert payload.encode_row(state, 1, (-1, -1), 0, ()) == 4539059951108097
    slots = (refinement.Slot(1, 0, 1, 1), refinement.Slot(1, 1, 2, 0))
    bits = payload.encode_row(state, 1, (-1, -1), 0, slots)
    assert bits == 5483081011333839697362526147398598657
    assert payload.decode_row(bits) == (state, 1, (-1, -1), 0, slots)
    with pytest.raises(payload.InvalidCertificate, match='hidden payload'):
        payload.decode_row(bits+(1 << (80+23*2)))
    with pytest.raises(payload.InvalidCertificate, match='nonnegative exact integer'):
        payload.decode_row(True)
    with pytest.raises(payload.InvalidCertificate, match='slot field overflow'):
        payload.encode_row(state, 1, (-1, -1), 0, (refinement.Slot(0, 15, 0, 0),))


@pytest.mark.parametrize('fixture', [0, 1])
def test_observed_complete_payload_negative_controls(fixture):
    _, records = inputs()
    observed = payload.negative_controls(records[fixture])
    assert len(observed) == 16
    assert all(control['rejected'] for control in observed.values())
    assert 'omitted_repeated_positional_edge' in observed
    assert 'removed_ancestor_and_all_stored_edges' in observed
    assert 'wrong_lookup_identity' in observed
    assert 'packed_orientation_mismatch' in observed


def test_complete_native_packet_and_single_fixture_scope():
    text, records = inputs()
    result = payload.verify_native(text)
    assert result['all_two_original_fixtures_verified']
    assert result['kernel_acceptance_supplied_by_this_oracle'] is False
    first = 'schema '+payload.SCHEMA+'\n'+'\n'.join(payload.payload_lines(records[0]))+'\n'
    one = payload.verify_native(first, fixture=0)
    assert one['all_two_original_fixtures_verified'] is False
    assert len(one['fixtures']) == 1
    with pytest.raises(payload.InvalidCertificate):
        payload.verify_native(first)


def test_parser_refuses_omitted_duplicate_or_cross_source_records():
    text, _ = inputs()
    lines = text.splitlines()
    first_slot = next(i for i, line in enumerate(lines) if line.startswith('slot '))
    first_packed = next(i for i, line in enumerate(lines) if line.startswith('packed '))
    first_lookup = next(i for i, line in enumerate(lines) if line.startswith('lookup '))
    for i in (first_slot, first_packed, first_lookup, len(lines)-1):
        changed = '\n'.join(lines[:i]+lines[i+1:])+'\n'
        with pytest.raises(payload.InvalidCertificate):
            payload.parse_payload(changed)
    with pytest.raises(payload.InvalidCertificate):
        payload.parse_payload(text+lines[-1]+'\n')
    with pytest.raises(payload.InvalidCertificate, match='lookup belongs'):
        payload.parse_payload(text.replace('lookup 0 ', 'lookup 1 ', 1))
    with pytest.raises(payload.InvalidCertificate, match='noncanonical'):
        payload.parse_payload(text.replace('graph 0 ', 'graph 00 ', 1))


def test_python_optimization_cannot_admit_truncated_payload():
    script = (
        f'import sys; sys.path.insert(0, {str(ROOT/"oracles/python")!r}); '
        'import c4_archived_payload as p; '
        "p.verify_native('schema '+p.SCHEMA+'\\n'); print('CERTIFIED')"
    )
    result = subprocess.run([sys.executable, '-O', '-c', script], capture_output=True, text=True)
    assert result.returncode != 0
    assert not result.stdout
    assert 'incomplete archived payload' in result.stderr
