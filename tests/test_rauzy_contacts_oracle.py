"""Independent reference-oracle replay for the Rauzy-contacts evidence bundle.

The Mojo kernel (kernel/psc/rauzy_contacts.mojo) is canonical; this replays
the committed `psc-rauzy-contacts/v1` records with the separately written
Python oracle, which builds the potential-overlap graph on a different region
(formal_overlap.FormalGraph), and pins the bundle digests. Covering degree 1 is
a cited consequence of the box verdict and is asserted nowhere here.
"""
import hashlib
import json
import runpy
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BUNDLE = ROOT / "evidence/rauzy-contacts-2026-10-22"
ORACLE = runpy.run_path(str(ROOT / "oracles/python/rauzy_contacts.py"))
#: Corpus records replayed here; the full corpus replays with the oracle's CLI.
CORPUS_SLICE = 6


def _records(name):
    return [json.loads(line) for line in (BUNDLE / name).read_text().splitlines()]


def _replay(mojo):
    sigma = [[int(c) for c in img] for img in mojo["sigma"]]
    ours = ORACLE["record"](sigma, mojo.get("coord_bits"))
    theirs = ORACLE["normalize"](mojo)
    assert {k: theirs.get(k) for k in ours} == ours, mojo.get("name", mojo.get("index"))


def test_bundle_digests():
    for line in (BUNDLE / "SHA256SUMS").read_text().splitlines():
        digest, name = line.split()
        assert hashlib.sha256((BUNDLE / name).read_bytes()).hexdigest() == digest


def test_every_named_record_matches_the_oracle():
    for mojo in _records("contacts-named.jsonl"):
        _replay(mojo)


def test_a_corpus_slice_matches_the_oracle():
    for mojo in _records("contacts-corpus.jsonl")[:CORPUS_SLICE]:
        _replay(mojo)


def test_tribonacci_has_six_lattice_neighbours_and_3742_twenty():
    named = {r["name"]: r for r in _records("contacts-named.jsonl")}
    assert len(named["tribonacci"]["lattice_neighbours"]) == 6
    assert len(named["specimen_3742"]["lattice_neighbours"]) == 20
    assert named["nonunit_control"]["status"] == "refused"


def test_every_unimodular_specimen_has_a_productive_box():
    corpus = _records("contacts-corpus.jsonl")
    assert len(corpus) == 4554
    exact = [r for r in corpus if r["status"] == "exact"]
    assert len(exact) == 2628 and all(r["box_productive"] for r in exact)
    assert all(r["regime"] == "nonunimodular" for r in corpus if r["status"] == "refused")
