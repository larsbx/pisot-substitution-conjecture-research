"""Missing load-bearing inventory fails closed; immutable packet checks elsewhere."""
import csv
import importlib.util
import json
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('below_integration', ROOT / 'oracles/python/check_class_c_below_three_integration.py')
ORACLE = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(ORACLE)


@pytest.mark.parametrize('name,c', [('plus', -15), ('minus', -7)])
def test_missing_required_bridge_refuses(name, c):
    plans = json.loads((ORACLE.PACKET / 'plan.json').read_text())
    plans[name]['lines'] = [r for r in plans[name]['lines'] if r['c'] != c]
    with pytest.raises(KeyError):
        ORACLE.check(plans=plans)


def test_missing_required_small_gap_member_refuses():
    records = list(csv.DictReader((ORACLE.PACKET / 'finite-members.csv').open()))
    records = [r for r in records if (r['sign'], r['d'], r['n']) != ('minus', '18', '53')]
    with pytest.raises(AssertionError, match='missing finite member'):
        ORACLE.check(records=records)


def test_accepts_real_inventory():
    assert len(ORACLE.check()) == 2
