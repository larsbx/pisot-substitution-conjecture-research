#!/usr/bin/env python3
"""Build tla/ledger.json from the record table below and regenerate every ledger surface.

The table is the single source of the proof-dependency ledger: one proof
record per named result (kind, statement, source, dependencies, tags), the
assumption sets the TLC models bind, the status labels the index prints, and
the aliases and prose surfaces each claim keeps in claim_governance.toml.
`tools/proof_records/generate_ledgers.py` (vendored from larsbx/finite-math-
kernels, docs/ledger-generation-spec.md there) renders tla/Ledger.tla, one
TLC model per assumption set, docs/ledger-index.md, and the generated
[[claim]] block of claim_governance.toml. CI runs `--check`, so none of those
surfaces can drift from this table or be hand-edited.

Usage: make_ledger.py [--check]
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "tools"))

from proof_records import generate_ledgers as gl  # noqa: E402
from proof_records.records import Edge, Kind, Record, identified  # noqa: E402

LEDGER = ROOT / "tla" / "ledger.json"
POLICY = ROOT / "claim_governance.toml"
SCOPE = "primitive irreducible Pisot substitutions in the standing regime"
MANUSCRIPT = "manuscripts/PSC_balanced_pair_state_2026-09-13.tex"
MAP = "docs/claim-status-and-source-map-2026-09-13.md"
LEDGER_DOC = "docs/conjecture-ledger.md"
WEEKLY = "docs/completion-ledger-2026-09-14.md"

# name -> (kind, statement, source or reason, dependencies, tags)
# Dependencies are one-way proof sufficiency, never a converse implication
# (tla/ProofArchitecture.tla). A proved node whose dependencies are open is a
# conditional theorem: its implication is proved, its premises are not.
T, I, P = Kind.REPOSITORY, Kind.IMPORTED, Kind.PENDING
TABLE: dict[str, tuple[Kind, str, str, tuple[str, ...], tuple[str, ...]]] = {
    # --- symbolic side, repository theorem-grade ------------------------------------
    "DefectTheorem": (T, "det M_sigma != 0 gives full incidence rank and letter injectivity, so the defect theorem applies to the image code",
                      f"{MANUSCRIPT}, standing algebraic setup", (), ()),
    "UniqueDecodability": (T, "the substitution images form a uniquely decodable code", f"{MANUSCRIPT}, Theorem 3.1", ("DefectTheorem",), ()),
    "UDForPowers": (T, "the images of every power sigma^r form a uniquely decodable code", f"{MANUSCRIPT}, power corollary of Theorem 3.1", ("UniqueDecodability",), ()),
    "LocalWitnessInjectivity": (T, "local witness injectivity on the symbolic side", f"{MANUSCRIPT}, symbolic side", (), ()),
    "MassBalanceK2Obstruction": (T, "the mass-balance obstruction for K2 on the symbolic side", f"{MANUSCRIPT}, symbolic side", (), ()),
    "AlgebraicEmbedding": (T, "the algebraic embedding of the symbolic side", f"{MANUSCRIPT}, symbolic side", ("UniqueDecodability",), ()),
    "WedgeBound": (T, "the wedge bound", f"{MANUSCRIPT}, symbolic side", ("AlgebraicEmbedding", "MassBalanceK2Obstruction"), ()),
    # --- seed spectral module ---------------------------------------------------------
    "PhiSemisimplicity": (T, "Phi_3 acts semisimply on the seed spectral module", "PscVerif/PscVerif/Spectral.lean", (), ()),
    "ThetaIntertwining": (T, "Theta intertwines the seed spectral operators", "PscVerif/PscVerif/Spectral.lean", (), ()),
    "SeedCentralizer": (T, "the seed centralizer is as certified", "PscVerif/PscVerif/Spectral.lean", ("ThetaIntertwining", "PhiSemisimplicity"), ()),
    "Target1": (T, "Target 1 of the seed spectral module", "PscVerif/PscVerif/Spectral.lean", ("SeedCentralizer",), ()),
    "DominantCubicCapture": (T, "dominant cubic capture for the explicitly certified seeds",
                             "archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md, sections 8-10 (historical restricted theorem)", ("Target1",), ()),
    "SpectralBlackBox": (T, "the seed-module spectral black box follows from Target 1 and dominant cubic capture",
                         "archive/2026-09-08/certificates_patched/PROOF_CERTIFICATE.md, sections 8-10", ("Target1", "DominantCubicCapture"), ()),
    # --- v33 / v34 historical route ---------------------------------------------------
    "InterBlockCancellation": (T, "inter-block cancellation on the v33/v34 route", f"{MANUSCRIPT}, historical route", (), ()),
    "DominantK2Source": (T, "the dominant K2 source on the v33/v34 route", f"{MANUSCRIPT}, historical route", (), ()),
    "LoadBearingSCC": (T, "under G1 the load-bearing SCC of the v33/v34 route exists", f"{MANUSCRIPT}, historical route",
                       ("G1", "DominantK2Source", "InterBlockCancellation"), ()),
    # --- live graph / C3-C4 reductions ---------------------------------------------
    "SinkSCCReduction": (T, "under G1, nonproductivity reduces to a finite closed sink recurrent noncoincident SCC", "docs/sink-scc-reduction.md", ("G1",), ()),
    "C3Locality": (T, "higher newborn cuts are one-step block-local", "docs/c3-locality-reduction.md", (), ()),
    "EndpointCore": (T, "the endpoint-core normal form classifies the finitely many endpoint maps", "docs/c4-endpoint-core-program.md", (), ()),
    "GlobalEndpointSync": (T, "global endpoint synchronization eliminates endpoint types A and B", "docs/c4-barge-diamond-endpoint-eliminator.md", ("EndpointCore",), ()),
    "SignatureReduction": (T, "the endpoint-quotient signature reduction", "docs/c4-signature-reduction.md", ("EndpointCore",), ()),
    "ParikhIntertwiner": (T, "for a finite closed nonproductive SCC the Parikh intertwiner identity P N = M P holds", "docs/c4-parikh-intertwiner.md", (), ()),
    "OrientationMonodromy": (T, "the orientation cocycle and oriented double cover dichotomy", "docs/c4-orientation-monodromy.md", (), ()),
    "OrientationSpectrum": (T, "the orientation-even/odd spectral decomposition with its Perron comparison", "docs/c4-orientation-spectrum.md",
                            ("OrientationMonodromy", "ParikhIntertwiner"), ()),
    "DefectIntertwiner": (T, "the signed scattered-subword defect intertwiners in degrees two and three", "docs/c4-lowest-defect-intertwiner.md", ("OrientationMonodromy",), ()),
    "W3LowGrowth": (T, "the universal low-growth classification in W_3", "docs/c4-w3-low-growth-and-interface-correction.md", ("DefectIntertwiner", "PhiSemisimplicity"), ()),
    "Degree4Floor": (T, "the degree-4 first-defect reduction", "docs/c4-degree4-free-lie.md", ("DefectIntertwiner",), ()),
    "Mod3Sieve": (T, "the arbitrary-degree multidegree spectral sieve", "docs/c4-multidegree-spectral-sieve.md", ("DefectIntertwiner",), ()),
    "ParitySieve": (T, "the degree-2 parity sieve for a strict closed nonproductive SCC with nonzero K2", "docs/c4-degree2-parity-sieve.md", ("DefectIntertwiner",), ()),
    "MidArea": (T, "the degree-2 mid-area factorization identity", "docs/c4-degree2-midarea-factorization.md", (), ()),
    "MeanAreaLift": (T, "the three-state mean-area lifting obstruction", "docs/c4-degree2-meanarea-integrality.md", ("MidArea", "ParikhIntertwiner"), ()),
    "LatticeLift": (T, "the degree-2 integral lattice lifting certificate", "docs/c4-degree2-lattice-lift.md", ("MeanAreaLift",), ()),
    # --- Level-2 gate ------------------------------------------------------------------
    "G1b1BoundedDiscrepancy": (T, "all reachable swap-state prefix-difference walks are uniformly bounded",
                               "docs/source-imports/issue-45/g1b1-bounded-discrepancy-reconstruction.md; manuscript Theorem 4.4; PR #69", (), ()),
    "G1b2RenewalFiniteness": (P, "only finitely many realizable irreducible balanced pairs occur inside the established discrepancy bound",
                              "open conjectural gate; manuscript Level-2 open problem; issue #44", ("G1b1BoundedDiscrepancy",), ()),
    "G1FromRenewal": (T, "G1b-1 and G1b-2 together give finite BPA", f"{MANUSCRIPT}, Proposition 4.11", ("G1b1BoundedDiscrepancy", "G1b2RenewalFiniteness"), ()),
    "G1": (T, "finite BPA (G1)", f"{MANUSCRIPT}, Proposition 4.11 and open-problem list", ("G1FromRenewal",), ("status:open",)),
    # --- overlap route (finite graph, no G1) ----------------------------------------
    "SwapOverlapFiniteness": (T, "every swap seed has a finite exact overlap graph",
                              "docs/overlap-finiteness-and-coincidence-density-2026-09-13.md; manuscript Theorem 4.22; PR #72", ("G1b1BoundedDiscrepancy",), ()),
    "OverlapFullRank": (T, "a nonempty child-closed noncoincidence set has full rational intersection-vector rank", f"{MANUSCRIPT}, Corollary 5.34; PR #76", (), ()),
    "OverlapBadSCCNormalForm": (T, "failure of overlap productivity has a finite child-closed recurrent nonproductive SCC with PF(N_S) = beta, full-rank V_S, and spec(M) inside spec(N_S)",
                                f"{MANUSCRIPT}, Proposition 5.43; docs/p1-overlap-minimal-obstruction-2026-09-14.md, Proposition 2.1; PR #88",
                                ("SwapOverlapFiniteness", "OverlapFullRank"), ()),
    "OverlapBoundaryZipperDichotomy": (T, "a bad SCC contains an offset-zero non-eventually-coincident pair or every child factorization is a strict no-tie prefix-grid zipper",
                                       f"{MANUSCRIPT}, Proposition 5.44 and Lemma 5.45; docs/p1-overlap-minimal-obstruction-2026-09-14.md, Proposition 3.1; PR #88",
                                       ("OverlapBadSCCNormalForm", "AlignedOverlapsAreStrongCoincidence", "BoundaryCoincidenceCriterion"), ()),
    "OverlapProductivity": (P, "for every PIP substitution one swap seed on distinct tile types has only productive reachable overlaps",
                            "open conjectural gate, the current shortest-path gate; manuscript Open Problem 5.35; issue #84", (), ()),
    "CoincidenceDensityOne": (T, "seedwise overlap productivity gives coincidence density one and a dense eventual-coincidence good set",
                              f"{MANUSCRIPT}, Lemma 5.36; PR #77", ("OverlapProductivity", "SwapOverlapFiniteness"), ("status:proved",)),
    "AllStatesProductiveViaOverlaps": (T, "under seedwise overlap productivity every reachable balanced-pair state is productive",
                                       f"{MANUSCRIPT}, overlap route", ("OverlapProductivity", "SwapOverlapFiniteness"), ()),
    "DensityToPDSBridge": (I, "dense eventual coincidence gives pure discrete spectrum", "Barge, Stimac, and Williams; manuscript Imported Theorem 5.37; PR #77", (), ()),
    "PDSOverlapRoute": (T, "one-seed overlap productivity implies pure discrete spectrum, without G1 and without a seed-legality hypothesis",
                        f"{MANUSCRIPT}, Theorem 5.38", ("CoincidenceDensityOne", "DensityToPDSBridge"), ()),
    "AlignedOverlapsAreStrongCoincidence": (T, "offset-zero and right-aligned seed overlaps are productive exactly in the prefix/suffix strong-coincidence cases",
                                            f"{MANUSCRIPT}, Proposition 5.39; PR #82", (), ()),
    "BoundaryCoincidenceCriterion": (T, "an overlap reaches an offset-zero descendant exactly on an exact prefix-Parikh / common-left-endpoint hit",
                                     f"{MANUSCRIPT}, Proposition 5.40 and Corollary 5.41; PR #82", (), ()),
    # --- strongest Level-3 spectral route ----------------------------------------------
    "ConcentrationAuxB": (P, "no strict component with K2 = 0 exists (concentration / aux-B)", "open conjectural gate, not source-pending; manuscript open problem; issue #43",
                          ("G1", "SinkSCCReduction"), ()),
    "GaloisWedgePropagation": (T, "nonzero K2 gives full rational wedge span (degree-two carrier span)",
                               f"{MANUSCRIPT}, Proposition 5.20; docs/galois-aux-b-source-resolution-2026-09-13.md; PR #68", (), ()),
    "SpanRichProductivity": (P, "no strict component with K2 != 0 exists (general wedge productivity)",
                             "open conjectural gate, not source-pending; manuscript open problem; issue #85", ("ConcentrationAuxB", "GaloisWedgePropagation"), ()),
    "SpectralSCCProducer": (P, "the spectral route produces an SCC producer under G1", "open; the spectral SCC producer is not proved even conditionally",
                            ("G1", "SinkSCCReduction", "SpanRichProductivity"), ()),
    "PDSSpectralRoute": (T, "under G1 and a spectral SCC producer, pure discrete spectrum follows", f"{MANUSCRIPT}, spectral route", ("G1", "SpectralSCCProducer"), ()),
    # --- open C4 sufficiency route -----------------------------------------------------
    "C4": (P, "the C4 hypothesis of the boundary route", "open sufficiency premise of the C4 route", (), ()),
    "C3Local": (T, "C4 gives C3-local", "docs/c3-locality-reduction.md", ("C4", "C3Locality"), ()),
    "C2": (T, "C3-local gives C2", f"{MANUSCRIPT}, boundary route", ("C3Local",), ()),
    "SCCProducer": (T, "SCC Producer / C1 follows from G1, the sink-SCC reduction, and C2", f"{LEDGER_DOC}; manuscript unresolved statements",
                    ("G1", "SinkSCCReduction", "C2"), ("status:open",)),
    "PDS": (T, "pure discrete spectrum follows from G1 and SCC Producer", f"{MANUSCRIPT}, boundary route", ("G1", "SCCProducer"), ()),
    # --- literature / repository BPA bridge ---------------------------------------
    "StandardBPAEquivalence": (I, "the standard balanced-pair algorithm criterion for pure discrete spectrum", "docs/bpa-literature-bridge.md and the literature cited there", (), ()),
    "RepoSeedUnionBridge": (T, "the repository seed-union graph is the union of the literature seed graphs", "docs/bpa-literature-bridge.md", (), ()),
    "PDSImpliesRepoG1": (P, "seedwise pure discrete spectrum implies repository G1", "open until the seedwise implication is pinned; docs/bpa-literature-bridge.md",
                         ("StandardBPAEquivalence", "RepoSeedUnionBridge"), ()),
    # --- retracted ------------------------------------------------------------------------
    "V5Thm51": (P, "v5 Theorem 5.1", "retired: the v5 Theorem 5.1 argument is withdrawn", (), (gl.WITHDRAWN_TAG,)),
}

STATUS_NOTES = {
    "G1": "the conditional assembly from G1b-1 and G1b-2 is proved; G1 itself is an open conjectural gate",
    "SCCProducer": "the implication from G1, the sink-SCC reduction, and C2 is proved; SCC Producer / C1 is an open theorem target",
    "CoincidenceDensityOne": "the equivalence of Lemma 5.36 is repository-proved; the ledger node is its conclusion, which needs overlap productivity",
}

ASSUMPTION_SETS = {
    "G1AndProducer": ["G1", "SCCProducer"],
    "G1Only": ["G1"],
    "G1AndC4": ["G1", "C4"],
    "RenewalGateAssumed": ["G1b1BoundedDiscrepancy", "G1b2RenewalFiniteness"],
    "SpectralGateAssumed": ["G1", "ConcentrationAuxB", "SpanRichProductivity", "SpectralSCCProducer"],
    # Imported theorems are established only by assumption (ImportedDef, never
    # ProvedDef), so the overlap gate names the Barge-Stimac-Williams import it
    # needs to reach PDSOverlapRoute.
    "OverlapGateAssumed": ["OverlapProductivity", "DensityToPDSBridge"],
}

STATUS_LABELS = {"proved": "Repository-proved", "imported": "Imported theorem", "conditional": "Conditional theorem", "open": "Open conjectural gate",
                 "retired": "Retired claim", "finite-domain": "Finite-domain theorem"}

ALIASES = {
    "DefectTheorem": ["FullIncidenceRank", "full incidence rank"], "UniqueDecodability": ["unique decodability"],
    "G1b1BoundedDiscrepancy": ["G1b-1", "bounded discrepancy"], "G1b2RenewalFiniteness": ["G1b-2", "renewal finiteness"], "G1": ["finite BPA"],
    "SinkSCCReduction": ["sink-SCC reduction"], "GaloisWedgePropagation": ["degree-two carrier span"], "ConcentrationAuxB": ["aux-B", "general concentration"],
    "SpanRichProductivity": ["general wedge productivity"], "SwapOverlapFiniteness": ["seed-patch overlap graph finiteness", "seed-patch overlap finiteness"],
    "OverlapFullRank": ["full-rank child-closed overlap constraint"], "OverlapBadSCCNormalForm": ["closed irreducible bad-overlap normal form"],
    "OverlapBoundaryZipperDichotomy": ["strict zipper dichotomy"], "CoincidenceDensityOne": ["coincidence density one"],
    "DensityToPDSBridge": ["density-to-PDS bridge", "Barge–Štimac–Williams theorem"], "PDSOverlapRoute": ["Theorem 5.38"],
    "AlignedOverlapsAreStrongCoincidence": ["endpoint-aligned overlaps"], "BoundaryCoincidenceCriterion": ["boundary-hitting criterion"],
    "OverlapProductivity": ["seedwise overlap productivity", "overlap productivity", "Open Problem 5.35"], "SCCProducer": ["SCC Producer"],
}


def surface(path: str, anchor: str, window_lines: int = 0) -> dict:
    return {"path": path, "anchor": anchor, "window_lines": window_lines}


SURFACES = {  # prose surfaces on which each claim's status is spelled out (labelled by the consumer vocabulary)
    "DefectTheorem": [surface(MAP, "| Full incidence rank from"), surface(LEDGER_DOC, "### Full incidence rank and unique decodability", 2)],
    "UniqueDecodability": [surface(MAP, "| Unique decodability of substitution images and powers |"), surface("README.md", "**Unique decodability:**")],
    "G1b1BoundedDiscrepancy": [surface(MAP, "| G1b-1 bounded discrepancy |"), surface(LEDGER_DOC, "### G1b-1 bounded discrepancy", 2),
                               surface(WEEKLY, "=> bounded discrepancy"), surface("README.md", "=> bounded discrepancy")],
    "G1b2RenewalFiniteness": [surface(MAP, "| G1b-2 renewal finiteness |"), surface(LEDGER_DOC, "### G1b-2", 2),
                              surface(WEEKLY, "=> [OPEN] G1b-2 renewal finiteness"), surface(WEEKLY, "| **P3** | G1b-2 renewal finiteness |")],
    "G1": [surface(MAP, "| Finite BPA, G1 |"), surface(LEDGER_DOC, "## C. Parallel programme — G1 / renewal finiteness", 4)],
    "SinkSCCReduction": [surface(MAP, "| Sink-SCC reduction under G1 |")],
    "GaloisWedgePropagation": [surface(MAP, "| Degree-two carrier span / wedge dichotomy |")],
    "ConcentrationAuxB": [surface(MAP, "| Concentration / aux-B |"), surface(LEDGER_DOC, "### Concentration / aux-B", 2), surface(WEEKLY, "| **P4** | General concentration")],
    "SpanRichProductivity": [surface(MAP, "| General wedge productivity |"), surface(LEDGER_DOC, "### Wedge productivity", 2), surface(WEEKLY, "| **P5** | General wedge productivity")],
    "SwapOverlapFiniteness": [surface(MAP, "| Seed-patch overlap graph finiteness |"), surface(LEDGER_DOC, "### Seed-patch overlap finiteness", 2),
                              surface(WEEKLY, "=> finite seed-patch overlap graph"), surface("README.md", "=> finite seed-patch overlap graph")],
    "OverlapFullRank": [surface(MAP, "| Full-rank child-closed overlap constraint |"), surface(LEDGER_DOC, "### Full-rank constraint on a bad set", 2)],
    "OverlapBadSCCNormalForm": [surface(MAP, "| Closed irreducible bad-overlap normal form |"), surface(LEDGER_DOC, "### Closed irreducible bad-overlap normal form", 2)],
    "OverlapBoundaryZipperDichotomy": [surface(MAP, "| Boundary obstruction / strict zipper dichotomy |")],
    "CoincidenceDensityOne": [surface(MAP, "| Coincidence density / dense-good-set equivalence |"), surface(WEEKLY, "=> coincidence density one / dense good set"),
                              surface("README.md", "=> coincidence density one / dense good set")],
    "DensityToPDSBridge": [surface(MAP, "| Density-to-PDS bridge |"), surface(WEEKLY, "=> pure discrete spectrum"), surface("README.md", "=> pure discrete spectrum")],
    "PDSOverlapRoute": [surface(MAP, "| One-seed overlap productivity implies PDS |")],
    "AlignedOverlapsAreStrongCoincidence": [surface(MAP, "| Endpoint-aligned overlaps = strong-coincidence boundary cases |")],
    "BoundaryCoincidenceCriterion": [surface(MAP, "| Boundary-hitting criterion |")],
    "OverlapProductivity": [surface(MAP, "| Seedwise overlap productivity / Open Problem 5.35 |"), surface(LEDGER_DOC, "### Overlap productivity / Open Problem 5.35", 2),
                            surface(WEEKLY, "=> one swap seed has only productive reachable overlaps"), surface("README.md", "=> one swap seed has only productive reachable overlaps"),
                            surface(WEEKLY, "| **P1** | **Seedwise overlap productivity")],
    "SCCProducer": [surface(MAP, "| SCC Producer / C1 |")],
}


def records() -> dict[str, Record]:
    built: dict[str, Record] = {}

    def build(name: str) -> Record:
        if name in built:
            return built[name]
        kind, statement, source, deps, tags = TABLE[name]
        edges = tuple(Edge(build(d).id, build(d).statement, f"{name}/{d}") for d in deps)
        if kind is Kind.PENDING:
            evidence = (("reason", source),)
        elif kind is Kind.IMPORTED:
            evidence = (("hypotheses_checked", "true"), ("source", source))
        else:
            evidence = (("proof_reviewed", "true"), ("source", source))
        if name in STATUS_NOTES:
            evidence += (("status_note", STATUS_NOTES[name]),)
        built[name] = identified(Record("", kind, statement, SCOPE, edges, evidence, frozenset(tags)))
        return built[name]

    return {name: build(name) for name in TABLE}


def record_json(record: Record) -> dict:
    return {"id": record.id, "kind": record.kind.value, "statement": record.statement, "scope": record.scope,
            "depends_on": [[e.record_id, e.expected_claim, e.use_site, e.scope_relation, e.required_outcome] for e in record.depends_on],
            "evidence": [list(kv) for kv in record.evidence], "tags": sorted(record.tags)}


def ledger() -> dict:
    return {
        "format": gl.FORMAT,
        "repository": "larsbx/pisot-substitution-conjecture-research",
        "module": "Ledger",
        "tla_dir": "tla",
        "index_path": "docs/ledger-index.md",
        "assumption_sets": ASSUMPTION_SETS,
        "status_classes": {Kind.VERIFIED.value: "finite-domain"},
        "status_labels": STATUS_LABELS,
        "aliases": ALIASES,
        "surfaces": SURFACES,
        "records": {name: record_json(r) for name, r in records().items()},
    }


def main(argv: list[str]) -> int:
    check = "--check" in argv[1:]
    text = json.dumps(ledger(), indent=2, ensure_ascii=False) + "\n"
    if check:
        if not LEDGER.exists() or LEDGER.read_text(encoding="utf-8") != text:
            print(f"stale: {LEDGER} (run scripts/make_ledger.py)")
            return 1
    else:
        LEDGER.write_text(text, encoding="utf-8")
    args = ["generate_ledgers", str(LEDGER), "--out", str(ROOT), "--claims", str(POLICY)] + (["--check"] if check else [])
    return gl.main(args)


if __name__ == "__main__":
    sys.exit(main(sys.argv))
