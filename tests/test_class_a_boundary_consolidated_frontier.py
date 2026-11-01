"""Guard the two-image frontier inventory against false closure/typing."""
import importlib.util
from pathlib import Path
import pytest

FILE = Path(__file__).resolve().parents[1] / "oracles/python/class_a_boundary_consolidated_frontier.py"
spec = importlib.util.spec_from_file_location("consolidated_frontier", FILE)
audit = importlib.util.module_from_spec(spec)
spec.loader.exec_module(audit)


def test_canonical_partition_and_original_occurrence_receipts():
    record = audit.probe()
    assert record["union"] == 59
    assert record["intersection"] == 20
    assert record["tx_only"] == 22
    assert record["registered_sources"] == 24
    assert record["typed_terminal"] == 1
    assert record["unclassified_in_this_registry"] == 34
    assert len(record["frontier_review_labels"]) == 34
    assert record["forward_closed"] is False
    assert record["universal_BH"] is False


def test_oriented_identity_and_endpoint_controls():
    assert audit.reverse(audit.reverse((0, 2, 1, -1, 1))) == (0, 2, 1, -1, 1)
    assert audit.reverse((2, 2, -1, 1, 1)) == (2, 2, 1, -1, -1)
    assert (2, 0, 0, -1, 1) != (2, 0, 0, -1, 2)
    assert audit.C != audit.CY
    assert audit.C != audit.CC
    record = audit.snapshot()
    assert list(audit.CY) in record["frontier_review_labels"]
    assert list(audit.CC) in record["frontier_review_labels"]


def test_actual_index_and_wrong_type_cannot_fake_a_coincidence():
    g = audit.source_module("children")["Geometry"](-1, 0, 0)
    y0 = (2, 2, 1, -1, -1)
    assert g.child(y0, g.n, g.n) == audit.CC
    assert g.child(y0, g.n, g.n) != (1, 2, 0, -2, 3)
    v1 = (2, 0, 0, -1, 1)
    assert g.child(v1, 1, 1) != audit.C
    with pytest.raises(ValueError):
        g.child(v1, 1, 10**6)
