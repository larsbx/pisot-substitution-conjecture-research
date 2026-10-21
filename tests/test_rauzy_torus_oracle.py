"""Independent reference-oracle replay for the Rauzy-torus evidence bundle.

The Mojo kernel (kernel/psc/rauzy_torus.mojo) is canonical; this replays every
committed `psc-rauzy-torus/v1` record with the separately written exact Python
oracle and pins the bundle digests. Records are diagnostic: a lift profile is
a finite sample and certifies no covering degree.
"""
import hashlib
import json
import runpy
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "evidence/rauzy-torus-2026-10-21"
ORACLE = runpy.run_path(str(ROOT / "oracles/python/rauzy_torus.py"))


def _records(name):
    return [json.loads(line) for line in (BUNDLE / name).read_text().splitlines()]


def test_bundle_digests():
    for line in (BUNDLE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split()
        assert hashlib.sha256((BUNDLE / name).read_bytes()).hexdigest() == digest


@pytest.mark.parametrize("name", ["named.jsonl", "corpus.jsonl"])
def test_every_record_matches_the_oracle(name):
    for mojo in _records(name):
        sigma = [[int(c) for c in img] for img in mojo["sigma"]]
        ours = ORACLE["record"](sigma, mojo.get("points", 1), mojo.get("grid", 1), mojo.get("coord_bits"))
        assert {k: mojo.get(k) for k in ours} == ours, mojo.get("name", mojo.get("index"))


def test_status_is_diagnostic_or_refused():
    for mojo in _records("named.jsonl") + _records("corpus.jsonl"):
        assert mojo["schema"] == "psc-rauzy-torus/v1"
        assert mojo["status"] in {"diagnostic", "refused"}
        assert (mojo["status"] == "refused") == (mojo["regime"] == "nonunimodular")


def test_nonunit_control_is_refused():
    control = next(r for r in _records("named.jsonl") if r["name"] == "nonunit_control")
    assert control["status"] == "refused"
    assert "x" not in control
