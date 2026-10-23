"""Guard complete native receipts, all finite members, and scope boundaries."""
import re
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/issue139-gap5-2026-10-23'


@pytest.mark.parametrize('side,eps,first', [('plus', 1, 0), ('minus', -1, 3)])
def test_a_pilot_has_every_member_and_never_claims_the_whole_line(side, eps, first):
    text = (PACKET / f'a-{side}.log').read_text()
    assert (PACKET / f'a-{side}.exit').read_text().strip() == '0'
    rows = [tuple(map(int, m)) for m in re.findall(r'^SUMMARY (\d+) (\d+) (\d+) (\d+)$', text, re.M)]
    assert [r[0] for r in rows] == list(range(first, 13))
    assert all(0 < vertices < 20000 and 0 <= recurrent <= vertices and depth >= 0
               for _, vertices, depth, recurrent in rows)
    assert text.rstrip().endswith(
        f'CLASS_A_GAP_FIVE_FINITE eps= {eps} first= {first} last=12 whole_line_certified=false universal_139=false')


@pytest.mark.parametrize('side,eps,first', [('plus', 1, 5), ('minus', -1, 11)])
def test_c_certificate_completes_symbolic_prefix_and_both_cross_checks(side, eps, first):
    text = (PACKET / f'c-{side}.log').read_text()
    assert (PACKET / f'c-{side}.exit').read_text().strip() == '0'
    validate_c_receipt(text, eps, first)


def validate_c_receipt(text, eps, first):
    m = re.search(r'^CLASS_C_GAP_FIVE eps= (-?\d+) q0= (\d+) vertices= (\d+) sign_reads= (\d+) '
                  r'prefix_pip= (\d+) prefix_non_pip= (\d+) prefix_outside= (\d+) '
                  r'all_admissible_members_hit=true universal_139=false$', text, re.M)
    assert m, 'a partial graph, refusal or timeout cannot count as a certificate'
    sign, floor, vertices, queries, pip, non_pip, outside = map(int, m.groups())
    assert sign == eps and queries > 0 and vertices > 0
    assert pip == floor - first
    assert outside == (4 if eps == 1 else 6)
    assert non_pip == (1 if eps == 1 else 5)
    assert pip + non_pip + outside == floor
    expanded = [int(n) for n in re.findall(r'^BEGIN_SYMBOLIC_VERTEX (\d+) ', text, re.M)]
    assert expanded == list(range(vertices))
    prefix = [(int(n), int(total)) for n, total in re.findall(r'^BEGIN_LINE_PREFIX (\d+) of (\d+)$', text, re.M)]
    assert prefix == [(n, floor) for n in range(floor)]
    checks = [int(n) for n in re.findall(r'^BEGIN_LINE_CROSS_CHECK (\d+)$', text, re.M)]
    assert checks == [floor, floor + 5]
    assert text.rstrip().endswith(m.group())


def test_endpoint_controls_and_hosted_replay_are_not_just_historical_logs():
    assert (PACKET / 'domains.exit').read_text().strip() == '0'
    assert 'contract-receipt: gap-five A/C exact PIP endpoints' in (PACKET / 'domains.log').read_text()
    workflow = (ROOT / '.github/workflows/gap-five-evidence.yml').read_text()
    for item in ('eps: 1', 'eps: -1', 'mojo build -I . class_c_gap_five.mojo',
                 'timeout 1200 build/gap-five/c', 'diff ../evidence/issue139-gap5',
                 'set -euo pipefail', 'tests/test_gap_five_domains.mojo'):
        assert item in workflow


@pytest.mark.parametrize('mutation', ['truncate', 'vertex_count', 'sign', 'missing_prefix', 'missing_cross_check'])
def test_partial_or_corrupted_c_receipts_cannot_pass(mutation):
    text = (PACKET / 'c-plus.log').read_text()
    if mutation == 'truncate':
        text = text[:text.index('CLASS_C_GAP_FIVE')]
    elif mutation == 'vertex_count':
        text = re.sub(r'(CLASS_C_GAP_FIVE.*vertices= )\d+', r'\g<1>0', text)
    elif mutation == 'sign':
        text = text.replace('CLASS_C_GAP_FIVE eps= 1', 'CLASS_C_GAP_FIVE eps= -1')
    elif mutation == 'missing_prefix':
        text = re.sub(r'^BEGIN_LINE_PREFIX 0 of .*\n', '', text, flags=re.M)
    else:
        text = re.sub(r'^BEGIN_LINE_CROSS_CHECK .*\n', '', text, count=1, flags=re.M)
    with pytest.raises(AssertionError):
        validate_c_receipt(text, 1, 5)
