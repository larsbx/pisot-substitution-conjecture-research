"""Exercise only the pinned receipt parser; this is not a Lean acceptance run."""
from pathlib import Path
from datetime import datetime, timezone
import ast
import hashlib
import json
import subprocess
import sys
import tempfile

scratch = Path('/workspace/scratch/7dc9ab659e7f')
root = scratch / 'psc'
gate = root / 'tools/check_class_a_literal_entry.sh'
audit = scratch / 'literal-audit-trace-final.log'
blocks = [piece.split('\nPY\n', 1)[0] for piece in gate.read_text().split("<<'PY'\n")[1:]]
assert len(blocks) == 3
for block in blocks:
    ast.parse(block)
parser = blocks[-1]
prefix = 'PSC_CLASS_A_LITERAL_ENTRY'
raw = audit.read_text()
rows = [line for line in raw.splitlines() if prefix in line]
assert len(rows) == 41
endpoint_indices = [i for i, row in enumerate(rows) if row.startswith(prefix + '_ENDPOINT\t')]
assert len(endpoint_indices) == 33
first_endpoint, last_endpoint = endpoint_indices[0], endpoint_indices[-1]

def replace_row(index, replacement):
    changed = list(rows)
    changed[index] = replacement
    return '\n'.join(changed) + '\n'

fixtures = {
    'empty_log': '',
    'completion_without_proofs': rows[-1] + '\n',
    'omitted_module': '\n'.join(rows[1:]) + '\n',
    'duplicated_module': '\n'.join([rows[0], *rows]) + '\n',
    'wrong_module_identity': replace_row(0, rows[0].replace('ClassAMinusLiteralArithmetic', 'ForeignModule')),
    'wrong_module_count': replace_row(0, rows[0].replace('\t34\t26', '\t33\t26')),
    'zero_module_count': replace_row(0, rows[0].replace('\t34\t26', '\t0\t26')),
    'extra_module_field': replace_row(0, rows[0] + '\textra'),
    'omitted_traced_endpoint': '\n'.join(row for i, row in enumerate(rows) if i != last_endpoint) + '\n',
    'duplicated_endpoint': replace_row(last_endpoint, rows[last_endpoint-1]),
    'foreign_endpoint': replace_row(last_endpoint, prefix+'_ENDPOINT\tPsc.Foreign.fake'),
    'extra_endpoint_field': replace_row(first_endpoint, rows[first_endpoint] + '\textra'),
    'missing_completion': '\n'.join(rows[:-1]) + '\n',
    'duplicated_completion': '\n'.join([*rows, rows[-1]]) + '\n',
    'incomplete_negative_controls': replace_row(len(rows)-1, prefix+'_AUDIT_COMPLETE\t33\t98'),
    'malformed_negative_count': replace_row(len(rows)-1, prefix+'_AUDIT_COMPLETE\t33\t099'),
    'inconsistent_declaration_total': replace_row(6, prefix+'_DECLARATIONS\t6\t251\t174'),
    'reordered_success': '\n'.join([rows[-1], *rows[:-1]]) + '\n',
    'indented_duplicate_success': '\n'.join([*rows, ' '+rows[-1]]) + '\n',
    'unexpected_success_tag': '\n'.join([*rows, prefix+'_SUCCESS\t1']) + '\n',
    'prior_weaker_audit': (scratch/'literal-audit-dev2.log').read_text(),
}
started = datetime.now(timezone.utc).isoformat()
with tempfile.TemporaryDirectory(prefix='psc-literal-entry-parser-') as tmp:
    tmp = Path(tmp)
    baseline = tmp/'valid.log'
    baseline.write_text(raw)
    good = subprocess.run([sys.executable, '-c', parser, str(baseline)], capture_output=True, text=True)
    # The successful baseline is checked before entering the rejection loop.
    if good.returncode != 0:
        raise SystemExit('positive parser baseline failed: '+good.stdout+good.stderr)
    results = []
    for name, contents in fixtures.items():
        path = tmp/(name+'.log')
        path.write_text(contents)
        run = subprocess.run([sys.executable, '-c', parser, str(path)], capture_output=True, text=True)
        if run.returncode == 0:
            raise SystemExit('corrupted receipt accepted: '+name)
        results.append(dict(name=name, input_sha256=hashlib.sha256(contents.encode()).hexdigest(),
                            exit_code=run.returncode, refusal=(run.stdout+run.stderr).strip()))
report = dict(scope='receipt-parser controls only; not isolated Lean or hosted acceptance',
              started_utc=started, ended_utc=datetime.now(timezone.utc).isoformat(),
              gate=str(gate.relative_to(root)), gate_sha256=hashlib.sha256(gate.read_bytes()).hexdigest(),
              parser_sha256=hashlib.sha256(parser.encode()).hexdigest(),
              audit_log=str(audit), audit_log_sha256=hashlib.sha256(audit.read_bytes()).hexdigest(),
              positive_baseline_exit=good.returncode, rejected_mutations=len(results),
              controls=results, accepted=True)
out=scratch/'trace-gate-parser-controls.json'
out.write_text(json.dumps(report, sort_keys=True, indent=2)+'\n')
print(json.dumps(dict(report=str(out), positive_baseline_exit=good.returncode,
                      rejected_mutations=len(results), accepted=True)))
