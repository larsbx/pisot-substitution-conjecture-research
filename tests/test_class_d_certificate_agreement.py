"""Independent reconciliation of two distinct class-D certificate contracts.

The full template proves all labelled directed support for minus b=0,a>=4;
the target-aware spine proves a seed-containing child-closed upper cover and
one exact affine occurrence path per positive-rank state for a>=2. Agreement
is corroboration, not a universal theorem for b>0 or an executable Mojo receipt.
"""
import json
from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "oracles/python"))
import class_d_minus_certificate as spine
import class_d_boundary_template as full_oracle


def test_two_parametric_candidates_agree_on_labels_ranks_and_selected_edges():
    full = json.loads((ROOT / "evidence/class-d-minus-template-2026-10-14/oracle.json").read_text())
    rows = json.loads((ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json").read_text())["rows"]

    # Verify the spine's UNIVERSAL geometry, full-child upper closure,
    # whole-parameter occurrence indices, and strict rank descent first.
    assert spine.verify(rows) == {
        "states": 145, "targets": 6, "seed_occurrences": 9,
        "closure_candidates": 18779, "max_rank": 4,
    }
    # Independently regenerate the complete directed support for a>=4.
    generated = full_oracle.report()
    assert generated == full

    index = {tuple(v): i for i, v in enumerate(full["vertices"])}
    assert len(index) == len(rows) == 145
    assert set(index) == {tuple(r[:5]) for r in rows}
    for row in rows:
        i = index[tuple(row[:5])]
        assert row[5] == full["depths"][i]
        if row[5]:
            child = tuple(rows[row[6]][:5])
            assert index[child] in full["adjacency"][i]


def test_class_d_residual_coverage_partition_is_exact_on_integer_controls():
    # The theorem is algebraic (inverse formulas below). Finite controls
    # guard sign swaps, +1/-1 parameter confusion, and a missing b=0 edge.
    for s in (-1, 1):
        for a in range(0, 40):
            for b in range(0, 17):
                if s == -1:
                    p, q, r = 5 + 3*a + b, 6 + 3*a + b, 4 + 2*a + b
                else:
                    p, q, r = 3 + 3*a + b, 2 + 3*a + b, 2*a + b
                d = q-r
                assert p-q == s
                assert d >= 2 and a == d-2
                assert b == r-2*d+2*s+2
                assert 2*q-2*s-3*r-3 == -b-1
                assert r < q-1
                # Both b=0 boundaries are covered by the branch certificates,
                # not by extrapolating a sampled b>0 interior point.
                if b == 0:
                    assert (r == 2*a+4) if s == -1 else (r == 2*a)


def test_naive_positive_b_extension_changes_a_selected_edge():
    # The minus b=0 spine contains the c/y state w=(-2,4,-3) whose chosen
    # child reads both FIRST occurrences. That edge is exact for b=0 only.
    # Increasing positive-b contributes b*(sum w)*e_y, here -b*e_y.
    # No first-occurrence prefix depends on b. This is a strict algebraic
    # refusal of a literal reuse of this selected edge at b>=1, NOT a
    # counterexample to BH or to a different target-aware b>=1 certificate.
    rows = json.loads((ROOT / "evidence/class-d-target-spine-2026-10-14/certificate.json").read_text())["rows"]
    row = next(r for r in rows if r[:5] == [1, 2, -2, 4, -3])
    assert row[5] > 0 and row[7:11] == [0, 0, 0, 0]
    w = row[2:5]
    assert sum(w) == -1
    for a in (2, 3, 8):
        def mv(b):
            p, q, r = 3*a+5+b, 3*a+6+b, 2*a+4+b
            return [w[0]+w[1],
                    w[0]+w[1]+2*w[2],
                    p*w[0]+q*w[1]+r*w[2]]
        at_boundary, at_interior = mv(0), mv(1)
        assert at_interior == [at_boundary[0], at_boundary[1], at_boundary[2]-1]
