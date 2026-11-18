"""Universal coefficient and original-index rejection controls."""
from copy import deepcopy
from pathlib import Path
import runpy

import pytest

O = runpy.run_path(str(Path(__file__).resolve().parents[1] /
                      "oracles/python/class_a_minus_constant_symbolic.py"))


def test_exhaustive_all_height_run_chambers():
    packet = O["certify"]()
    assert packet["parameter_chambers"] == 2
    assert packet["directed_paths"] == 4
    assert packet["checked_edges"] == 12
    assert packet["literal_RUN_occurrences"] == 24
    assert packet["all_height_decrement"]
    assert all(packet["negative_controls"].values())
    assert len(packet["negative_controls"]) == 8
    assert all(row["full_original_prefix_identity"] for row in packet["paths"])


def test_changed_full_source_is_not_hidden_by_final_height():
    case = deepcopy(O["cases"]()[0])
    case["source"] = (2, 2, 1, -1, 1)
    with pytest.raises(ValueError, match="coefficient identity"):
        O["certify_path"](case)


def test_wrong_typed_endpoint_is_rejected():
    case = deepcopy(O["cases"]()[0])
    case["expected"][-1] = (2, 0, 0, 0, 0)
    with pytest.raises(ValueError, match="actual RUN"):
        O["certify_path"](case)


def test_unbounded_parameter_density_certificate():
    result = O["certify_density_and_recurrence"]()
    assert result["parameter_chamber"] == "d=5+u, n=6+u+v; u,v>=0"
    assert len(result["literal_density_margins"]) == 3
    assert len(result["root_guards"]) == 4
    assert len(result["density_gap_guards"]) == 3
    assert result["constant_central_interval"] == "2*d*abs(H)<=n"
