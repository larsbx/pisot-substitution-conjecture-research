"""Local controls for non-destructive PR #487 source/governance integration."""
import importlib.util
from pathlib import Path
import pytest

spec = importlib.util.spec_from_file_location(
    "reconcile_pr487", Path(__file__).resolve().parents[1] / "tools/reconcile_pr487.py"
)
repair = importlib.util.module_from_spec(spec)
spec.loader.exec_module(repair)

@pytest.mark.parametrize("ours,theirs,expected", [
    ("root\nbranch\n", "root\nmain\n", "root\nmain\nbranch\n"),
    ("root\nsame\n", "root\nsame\n", "root\nsame\n"),
    ("root\n", "root\nmain\n", "root\nmain\n"),
    ("root\nbranch\n", "root\n", "root\nbranch\n"),
])
def test_append_only_preserves_both_histories(ours, theirs, expected):
    assert repair.merge_append_only("root\n", ours, theirs) == expected

@pytest.mark.parametrize("ours,theirs", [("edited\n", "root\nmain\n"),
                                        ("root\nbranch\n", "deleted\n")])
def test_historical_edits_refuse(ours, theirs):
    with pytest.raises(ValueError, match="append-only"):
        repair.merge_append_only("root\n", ours, theirs)

def bank(*rows):
    return {"source_statements": [{"source": p, "statement_heading": h} for p,h in rows],
            "claims": [{"name": "C4", "status": "open"}],
            "lean_declarations": [], "pins": {}, "input_digests": {}}

def test_inventory_preserves_main_and_branch_only_sources():
    repair.verify_inventory(bank(("main.md", "repaired")),
                            bank(("main.md", "old"), ("new.md", "scoped")),
                            bank(("main.md", "repaired"), ("new.md", "scoped")))

@pytest.mark.parametrize("generated", [bank(("new.md", "scoped")),
                                      bank(("main.md", "repaired"))])
def test_inventory_omission_refuses(generated):
    with pytest.raises(ValueError, match="lost"):
        repair.verify_inventory(bank(("main.md", "repaired")),
                                bank(("new.md", "scoped")), generated)

def test_claim_status_promotion_refuses():
    main = bank(("main.md", "scoped"))
    changed = bank(("main.md", "scoped"))
    changed["claims"][0]["status"] = "proved"
    with pytest.raises(ValueError, match="claims"):
        repair.verify_inventory(main, main, changed)
