"""Independent rational differential audit and refusal/scheduling regressions."""
import importlib.util
from pathlib import Path
import pytest

ROOT = Path(__file__).resolve().parents[1]
PACKET = ROOT / 'evidence/class-a-gap-sign-2026-10-23'
spec = importlib.util.spec_from_file_location('gap_sign_oracle', ROOT / 'oracles/python/class_a_gap_sign.py')
ORACLE = importlib.util.module_from_spec(spec)
spec.loader.exec_module(ORACLE)


def test_native_conversion_identity_and_accepted_bilinears_are_sound():
    assert (PACKET / 'native.exit').read_text().strip() == '0'
    text = (PACKET / 'native.log').read_text()
    assert ORACLE.audit(text) == (225, 225)
    for eps in (1, -1):
        assert f'GAP_SIGN_PSC eps= {eps} margins=4 H=1/25 U=1/5 closed_residual=true closure_proved=false' in text
    assert text.rstrip().endswith('or universal boundary hitting')


@pytest.mark.parametrize('mutation', ['coefficient', 'missing', 'duplicate', 'false_accept'])
def test_independent_oracle_rejects_corrupted_receipts(mutation):
    text = (PACKET / 'native.log').read_text()
    line = next(s for s in text.splitlines() if s.startswith('GAP_SIGN_COEFF '))
    if mutation == 'coefficient':
        fields = line.split()
        fields[-1] = str(ORACLE.F(fields[-1]) + 1)
        text = text.replace(line, ' '.join(fields))
    elif mutation == 'missing':
        text = text.replace(line+'\n', '')
    elif mutation == 'duplicate':
        text += '\n'+line+'\n'
    else:
        text = text.replace('GAP_SIGN_BILINEAR -1 0 0 0 0', 'GAP_SIGN_BILINEAR -1 0 0 0 1')
    with pytest.raises(ValueError):
        ORACLE.audit(text)


def test_sign_workflow_replays_all_kernel_inputs():
    text = (ROOT / '.github/workflows/class-a-gap-sign.yml').read_text()
    for token in ("'kernel/**'", 'mojo build -I . tests/test_class_a_gap_sign.mojo',
                  'set -euo pipefail', 'class_a_gap_sign.py', 'diff ', 'upload-artifact@v4'):
        assert token in text
