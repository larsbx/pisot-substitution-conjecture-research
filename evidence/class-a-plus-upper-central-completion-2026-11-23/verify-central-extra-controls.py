"""Independent finite central replay, depth bounds and counter-calibrations.

This script uses the existing secondary oracle. It is not the canonical kernel,
does not extend the declared native source grid, and proves no universal claim.
"""
import argparse
import copy
from fractions import Fraction
import hashlib
import importlib
import json
from pathlib import Path
import sys

parser = argparse.ArgumentParser(description=__doc__)
parser.add_argument('--root', type=Path, required=True)
parser.add_argument('--native', type=Path, required=True)
parser.add_argument('--transcripts', type=Path, required=True)
parser.add_argument('--output', type=Path, required=True)
args = parser.parse_args()
sys.path.insert(0, str(args.root/'oracles/python'))
O = importlib.import_module('class_a_plus_upper_recurrence_independent')
V = importlib.import_module('class_a_plus_upper_recurrence')
records = [json.loads(line) for line in args.transcripts.open()]
lookup = {(r['n'],r['J'],*r['source'][2:]):r for r in records}
assert len(lookup) == len(records) == 818
native_members = {}
native_rows = {}
for line in args.native.read_text().splitlines():
    if line.startswith('PLUS_UPPER_CENTRAL_PATH '):
        key, record = V.parse_row(line, native_members)
        assert key not in native_rows
        native_rows[key] = record
assert set(native_rows) == set(lookup)

maximum_cycle_height = maximum_cycle_depth = 0
central_bound_checks = suffix_bound_checks = full_bound_checks = 0
reversal_edge_checks = 0
for key, record in lookup.items():
    native_record = json.loads(json.dumps(native_rows[key]))
    assert native_record == record, ('independently selected path mismatch', key)
    n, J = record['n'], record['J']
    p,q,r = record['source'][2:]
    B = (n+7)*(abs(p)+abs(2*p+q+r)+1)
    assert B == record['B']
    K = (2*B+1)**2
    depth, central_depth = len(record['steps']), record['central_depth']
    assert central_depth <= K
    central_bound_checks += 1
    middle = record['source'] if central_depth == 0 else record['steps'][central_depth-1]['target']
    signed_height = O.cycle_height(middle)
    assert signed_height is not None
    H = abs(signed_height)
    assert J*H <= n-1
    suffix = depth-central_depth
    expected_suffix = (0 if H == 0 else 2*H if J >= 3 else
                       2*H+1 if J == 2 else 3 if H == 1 else 2*H-1)
    assert suffix == expected_suffix
    assert suffix <= 2*H+1 and suffix <= 2*n-1
    suffix_bound_checks += 1
    assert depth <= K+2*n-1
    full_bound_checks += 1
    maximum_cycle_height = max(maximum_cycle_height,H)
    maximum_cycle_depth = max(maximum_cycle_depth,suffix)
    reverse = lookup[(n,J,-p,-q,-r)]
    assert reverse['central_depth'] == central_depth
    assert len(reverse['steps']) == depth
    assert reverse['result']['P'] == record['result']['Q']
    assert reverse['result']['Q'] == record['result']['P']
    for edge, opposite in zip(record['steps'],reverse['steps']):
        assert edge['indices'] == opposite['indices'][::-1]
        a,b,*w = edge['target']
        assert opposite['target'] == [b,a,*(-x for x in w)]
        assert edge['top_prefix'] == opposite['bottom_prefix']
        assert edge['bottom_prefix'] == opposite['top_prefix']
        reversal_edge_checks += 1

member = O.LiteralMember(7,1)
cycle = (2,2,4,12,-24)
assert member.central(cycle)
current = cycle
cycle_edges = []
for _ in range(2):
    e = member.nearest_gap(current)
    indices = (1+max(e,0),1+max(-e,0))
    target, top, bottom = member.step(current,indices)
    assert member.central(target) and not O.zero(target)
    cycle_edges.append(dict(source=current, gap=e, indices=indices, target=target,
                            top_prefix=top,bottom_prefix=bottom))
    current = target
assert current == cycle
cycle_escape = O.emit(member,cycle)
O.replay(member,cycle_escape)
assert cycle_escape['central_depth'] == 0 and len(cycle_escape['steps']) == 7

delay_source = (2,2,1,2,-5)
delay = O.emit(member,delay_source)
O.replay(member,delay)
assert O.cycle_height(delay_source) is None
assert (delay_source[2],-(2*delay_source[2]+delay_source[3]+delay_source[4])) == (1,1)
assert delay['central_depth'] == 1
assert delay['steps'][0]['indices'] == (1,1)
assert delay['steps'][0]['target'] == (2,2,-1,-3,6)
early = copy.deepcopy(delay)
early['central_depth'] = 0
try:
    O.replay(member,early)
except ValueError as error:
    assert str(error) == 'cycle cutoff is not the full strictly central W packet'
    early_rejection = str(error)
else:
    raise AssertionError('premature full-packet reconstruction was accepted')

large_source = (2,2,0,1000,member.central_r(0,1000))
assert large_source == (2,2,0,1000,-917)
gap = member.nearest_gap(large_source)
indices = (1+max(gap,0),1+max(-gap,0))
large_target, top, bottom = member.step(large_source,indices)
assert member.central(large_source) and member.central(large_target)
assert gap == 3 and indices == (4,1) and large_target == (2,2,83,83,-339)
full_reserve = O.initial_reserve(member,large_source)
incomplete_reserve = (member.n+7)*(abs(large_source[2])+1)
assert full_reserve == 1176 and incomplete_reserve == 14
assert abs(large_target[2]) > incomplete_reserve

tie_error = abs(Fraction(0)-(-Fraction(1,8)*4+Fraction(1)*0))
assert tie_error == Fraction(1,2) and not tie_error < Fraction(1,2)
low_J_signs = {J:O.LiteralMember(7,J).sign_numerator((-4,J-4,0)) for J in range(1,5)}
assert set(low_J_signs.values()) == {-1}

oracle_path = args.root/'oracles/python/class_a_plus_upper_recurrence_independent.py'
result = {
    'scope':'finite independent calibration; universal claims require the separate Lean proof',
    'oracle_source_sha256':hashlib.sha256(oracle_path.read_bytes()).hexdigest(),
    'native_stdout_sha256':hashlib.sha256(args.native.read_bytes()).hexdigest(),
    'independent_jsonl_sha256':hashlib.sha256(args.transcripts.read_bytes()).hexdigest(),
    'native_and_independent_full_paths_identical':len(records),
    'central_depth_pair_count_checks':central_bound_checks,
    'signed_cycle_depth_formula_and_bound_checks':suffix_bound_checks,
    'full_depth_K_plus_2n_minus_1_checks':full_bound_checks,
    'maximum_signed_cycle_height':maximum_cycle_height,
    'maximum_cycle_suffix_depth':maximum_cycle_depth,
    'reversal_sources_checked':len(records),
    'reversal_edges_checked':reversal_edge_checks,
    'nonzero_actual_nearest_cycle':{'n':7,'J':1,'source':cycle,'edges':cycle_edges,
                                   'actual_alternative_exit_depth':7},
    'one_step_reconstruction_delay':{'n':7,'J':1,'source':delay_source,
                                    'transformed_initial_pair':(1,1),
                                    'first_edge':delay['steps'][0],
                                    'premature_cutoff_rejection':early_rejection},
    'both_initial_coordinates_required':{'n':7,'J':1,'source':large_source,
                                         'gap':gap,'indices':indices,'target':large_target,
                                         'top_prefix':top,'bottom_prefix':bottom,
                                         'full_reserve':full_reserve,
                                         'incomplete_p_only_reserve':incomplete_reserve},
    'synthetic_half_tie_control':{'A':'1/8','C':'1','input':[4,0,0],
                                  'absolute_error':'1/2','strict_nearest':False,
                                  'is_literal_integral_family_input':False},
    'low_J_absolute_contraction_reserve_signs':low_J_signs,
}
with args.output.open('x') as file:
    json.dump(result,file,indent=2)
    file.write('\n')
print(json.dumps({key:value for key,value in result.items()
                  if key not in ('nonzero_actual_nearest_cycle','one_step_reconstruction_delay',
                                 'both_initial_coordinates_required','synthetic_half_tie_control',
                                 'low_J_absolute_contraction_reserve_signs')},sort_keys=True))
