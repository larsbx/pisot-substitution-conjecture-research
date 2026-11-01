"""Comment/docstring pseudo-imports must not distort source provenance."""
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SPEC = importlib.util.spec_from_file_location('below_imports', ROOT / 'tools/check_class_c_below_three_imports.py')
GUARD = importlib.util.module_from_spec(SPEC)
SPEC.loader.exec_module(GUARD)


def test_ignores_documentation_but_keeps_indented_imports():
    source = '\"\"\"\nfrom the example import imaginary\n\"\"\"\n# import a\nfrom std.testing import assert_equal\ndef f():\n    from psc.exact import q_string\n'
    assert GUARD.import_modules(source) == ['std.testing', 'psc.exact']


def test_actual_import_closure_is_fully_pinned():
    result = GUARD.check()
    assert result['external_roots'] == ['max', 'std']
    assert not result['missing_or_stale_pins']
    assert result['local_source_count'] == 57
    expected = json.loads((ROOT / 'evidence/class-c-below-three-validation-2026-11-01/import-closure.json').read_text())
    assert result == expected
