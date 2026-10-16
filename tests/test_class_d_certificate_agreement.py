"""Cross-check concurrent exact-template and target-aware evidence without resampling."""
import json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1]


def test_two_parametric_candidates_agree_on_labels_ranks_and_selected_edges():
    full=json.loads((ROOT/'evidence/class-d-minus-template-2026-10-14/oracle.json').read_text())
    rows=json.loads((ROOT/'evidence/class-d-target-spine-2026-10-14/certificate.json').read_text())['rows']
    index={tuple(v):i for i,v in enumerate(full['vertices'])}
    assert len(index)==len(rows)==145
    assert set(index)=={tuple(r[:5]) for r in rows}
    for row in rows:
        i=index[tuple(row[:5])]
        assert row[5]==full['depths'][i]
        if row[5]:
            child=tuple(rows[row[6]][:5])
            assert index[child] in full['adjacency'][i]
