# Certificate index and independent replay

## Source and toolchain pins

```bash
git clone https://github.com/larsbx/pisot-substitution-conjecture-research.git psc
cd psc
git checkout --detach fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5
git rev-parse HEAD
python3 -m venv .venv
. .venv/bin/activate
python -m pip install pytest==8.3.5 pypdf==6.19.0 sympy==1.14.0
```

Mojo replay is specified by `kernel/pixi.toml` and `kernel/pixi.lock`. The Linux compiler is `1.1.0.dev2026090805` (build `34562fa1`). The SHA-256 of `kernel/pixi.lock` is `1515f7300f49ad6b5e263a9bc02a8ec041123ce455b28fd24c440022824b2ff8`. Reviewers can use the Pixi commands below. Local native receipts in this dossier use the matching compiler build with its extracted runtime and standard library, without resolving a fresh Pixi environment.

```bash
# Run from the checkout root. Pytest's separate implementation reconstructs
# literal word factors, addresses and counts instead of consuming native verdicts.
python -m pytest -o addopts='' -q tests/test_c4*oracle.py
python tools/make_proof_bank.py --check
bash tools/verify_all.sh provenance

# Run each native test separately, so a failed test preserves the other receipts.
cd kernel
for test_file in tests/test_c4*.mojo; do
  printf '\n== %s ==\n' "$test_file"
  pixi run --locked mojo run -I . -I tests "$test_file"
  printf 'exit status %s\n' "$?"
done
```

For each native test require an exit status of zero **and** its final contract receipt. An exhausted cap, malformed witness, omitted ordered child, or geometry mismatch is a refusal. Compare proofs and assertions even when both implementations agree.

## Exact certificates and mandatory negatives

| Fixture or proof | Exact data to preserve | What it calibrates or refutes | Replay stem |
|---|---|---|---|
| Forward and reversed run families | Eight witness formulas in the submission draft. At fixed \(s=4\), forward splittings \(a=0,1,2,3,4\) exhibit \((n,p)=(2,0),(3,6),(3,11),(3,16),(4,97)\). Exclude singular \((0,0)\). Forward native verifier bounds \(a,b\le16\), reverse bounds \(a,b\le8\), \(a+b\le12\). Tests exercise smaller grids | Literal order carries the witness. Identical incidence does not encode the displayed address. These depths give upper bounds. Full parameter coverage follows from the symbolic proof | `third_level_coincidence_family`; additional Python `reversed_run_family` |
| \(01/12/021\), productive unimodular ternary PIP, genuine good edge \(\{0,2\}\) | From \((10,01)\), depth one \((1201,0112)\), depth two \((1202101,0112120),(12,21)\). Phase words \([0]\) then \([0,0]\). Depth-two mass minor +1 and sole newborn at cut 7, digits \((3,0)/(3,1)\), defect \((0,-1,1)\), correction \((-1,0,0)\), neither side in Sync. Depth three has a right Sync newborn at cut 7 of the first depth-two child. Path \([0,0,1,0]\) reaches \((0,0)\) | Full rank and a genuine good edge plus flat nonsynchronization through depth two do not force synchronization by depth two. The system has a productive exit | `two_generation_rank`, `complete_cone_hub_audit` |
| \(11/210/10\), productive non-unit ternary PIP | Phase-one finite cone in §8 of the depth-two rank proof. Retain every listed ordered child, cut, and Parikh column | Finite-cone phase-one obstruction control. Its eventual productivity is compatible with no early synchronizing newborn | `two_generation_rank` and the literal §8 receipts |
| \(10/102/211\), strict primitive reducible control | Four-state literal component, all 16 ordered hub residuals zero, no synchronizing newborn. \(P\) has rank two, normal \(f=(1,0,-1)\) and \(fM=f\). \(\chi_M=(x-1)(x^2-2x-2)\). Sole represented cut pair \(\{1,2\}\) | A closed flat nonproductive carrier exists outside the irreducible Pisot hypotheses. The positive crossing bound and good-edge conclusions cannot be generalized to this example | `complete_cone_hub_audit`, `physical_hub_area`, `cut_pair_reduction` |
| \(1/02/220\), real-conjugate PIP with exits | Parent \((0222022012,1220220220)\), three ordered phase-one children, cut word \([0,10,17,23]\), child-mass determinant −1. Only child 0 returns and track-swaps. Exit path \([2,1]\) gives \((2,2)\). Good edge \(\{0,2\}\) has equal prefix \((1,0,2)\) followed by 2 at level four | Recurrence, even with a full flat row and no synchronized immediate newborn, cannot replace strict closure. The separated equal-index hub crossing is a different occurrence from the actual productive physical overlap (offset \(-e_0\), full diagonal cut 104) | `recurrent_flat_exits`, `cut_alignment`; [open #466](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/466) for physical address details |
| Addressed overlap transport | \(01/12/021\): path \([0,1,2]\), parent \((02112,21120)\), local cut 11, right Sync. \(1/02/220\): path \([2,2,1]\), parent \((202201,012202)\), local cut 4, right Sync. Left-exterior diagonal uses left Sync. Check both inherited-cut splitting and noncoincident endpoints | Reconstruct the first diagonal and exact one-step parent. Full inflated word cuts, parent-local cuts and symbolic source indices are different quantities | `addressed_newborn` |
| Physical area exact calibration | For integer widths \((2,3,5)\), signed areas \(-3,26,5\) and negative lengths \(5,5,0\) on the three named fixtures in source order. The oracle also exhausts short balanced oriented pairs | Exact integer check of the weighted area identity. The paper proof uses actual Perron lengths, with no integer substitution for those lengths | `physical_hub_area` |
| \(012/120/201\), genuine strict reducible control | Nine source occurrences and 81 source-to-target address routes. The three state pairs are formed by the three cyclic image rotations. \(N\) is all ones, \(\beta=3,L=(3,3,3)\), exact rate \(1/9\) for every represented cut pair. Removing two states violates all-child closure | Enclosure, support connectivity and positive frequency alone allow a genuine nonproductive sink. Rank-one incidence excludes PIP | `overlap_enclosure`, `cut_pair_reduction`, `pairwise_cut_frequency` |
| Synthetic period two | \(N=\begin{pmatrix}0&2\\2&0\end{pmatrix}\), class-0 normalized count alternates 1 and 0 from source 0 | Irreducible alone does not give a full-sequence positive per-pair limit. This is a matrix control | `pairwise_cut_frequency` |
| \(1/02/202\), real-secondary packet control, and \(1/2/021\), actual G/F | Actual packet cycle \(209\xrightarrow{396}429\xrightarrow{820}209\) with entry edge 91 and index drift \(0\to1\to0\). The actual G/F factor lengths \(1,2,5\) differ from the synthetic \(1,1,3\), including the literal \(2/2\) diagonal in the real support | Absolute offset monotonicity and algebraically guessed child counts fail even before the desired global implication. Packet recurrence and actual pair-system closure are different | Target-aware diagnostic and [offset negative](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/c4-ordered-hub-offset-negative-2026-10-06.md) |

For the C4 table, native files use `kernel/tests/test_c4_<stem>.mojo`. Independent tests use `tests/test_c4_<stem>_oracle.py`. The phase-one finite-cone source and the exact phase-zero cut details are in §§8–9 of the [two-generation rank note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/c4-two-generation-parikh-span-2026-11-02.md). The target-aware diagnostic's commands, historical counts and exact receipts are in the [diagnostic note](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/docs/target-aware-bpa-diagnostic-2026-10-02.md).

## Separate spectral and formal replays

**Theorem Ω.** Historical PR #233 exact source is `72f173dbc8dc0de1e5e13503b2911e0411d1fda8`. Its CI checkout `1c5128de9e4fab2c93f2493c99235f27bd663987` was recorded to have the identical tree `86c6b2a5274fca5105a26f1c2e961c8a1864440a`. The evidence directory contains the final 13-job CI record, independent domain-cardinality counts, original census excerpts, four representative graph receipts, deliberately corrupted graph rejections and SHA-256 verification. Clone the pinned source for the census. Use the dossier snapshot for the audit exporter if the exporter is absent from the historical checkout. The 12 length-four shard boundaries and the total-length command are in the pinned workflow. Check all shards report zero caps and failures and all enumerated boxes productive. The full census is historical evidence, and was not rerun during this dossier. [Audit packet and representative replay](https://github.com/larsbx/pisot-substitution-conjecture-research/tree/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/evidence/omega-box-audit-2026-10-08), [shard workflow](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/.github/workflows/box-automaton-evidence.yml).

```bash
# From repository root. Runs a finite representative replay and an independent count.
(cd kernel && pixi run --locked mojo run -I . omega_box_audit.mojo) > /tmp/psc-omega-boxes.txt
PYTHONPATH=reference python oracles/python/omega_box_audit.py /tmp/psc-omega-boxes.txt
PYTHONPATH=reference python oracles/python/omega_domain_audit.py
# Full census, example slices. Complete shard list is in the workflow.
(cd kernel && pixi run --locked mojo run -I . vertex_coincidence_census.mojo total)
(cd kernel && pixi run --locked mojo run -I . vertex_coincidence_census.mojo len4 0 11333)
```

**Finite Class A and Lean.** [PR #447 exact-head run](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41448531108) covers 22 named specimens, complete literal source/edge records and shortest terminal distances. [PR #448's audited Lean receipt](https://github.com/larsbx/pisot-substitution-conjecture-research/tree/fd3b64e2e25a7d8a7a8623a52677a8822e52f6c5/evidence/finite-quotient-distance-lean-2026-11-02) and its source digest pin the declarations checked. A fresh Lean replay was outside this dossier's runs. For independent reproduction run `./tools/setup_lean.sh` then `./tools/check_lean.sh` from the repository root with Lean `leanprover/lean4:v4.34.0-rc2` and Mathlib `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`. Require the isolated audit completion receipt and no unsupported axioms. For TLA+ set `TLA_TOOLS` to a valid TLC jar and use `bash proof/tla/check.sh` and read the corresponding `proof/tla/MCLedger*.cfg` premises before interpreting a pass.

## Replay findings and hosted receipts

- **Main Python and provenance.** Local pytest gave **57 passes and 2 failures**. Both failures are in `test_c4_cut_pair_reduction_oracle.py`, where the string letters look up an integer-keyed first-letter map. Main also rejected the generated proof bank as stale and reported a separate claim-governance failure because its declaration scanner did not recognize a claim or contract in the cut-frequency test. The native executable itself emitted its contract receipt. These are software or evidence-surface failures on the frozen revision. They leave the hypotheses of the word proofs as stated. The frozen run outputs are in the [replay archive](../../evidence/referee-dossier-2026-11-04/README.md).
- **Main native replay.** Nine of eleven focused C4 test programs passed using the pinned compiler build, including addressed transport, weighted area, enclosure, recurrent exits, Parikh rank and cut frequency. The cut-pair reduction aborts on malformed letter 3. Separately, the run-family checker does not compile: line 216 tries to implicitly copy a `List[Int]` at `reversed.append(new_word)`. In a detached diagnostic copy only, changing that line to `reversed.append(new_word^)` made the family suite pass. The included diff and log preserve this diagnostic distinction. The merged checker remains red at the audited source. The unmodified independent Python forward and reverse oracles passed.
- **Separate repair.** Open PR #485 at `b7c1f804cb258c23c88be30d69522ddaa618d210` gave **59 Python passes**, both targeted native passes and a passing proof-bank consistency command. The main native malformed-letter failure is the index-3 abort from calling the balance check before validating letters. The repair branch has a distinct receipt and adds a separate proposed occupancy result. Nothing from that branch is credited to main.
- **Transport #467.** [Focused run 41805682348](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41805682348) succeeded at source `4362c4a75e5218eddeebaf635cf2a36a7401037a`. The broad PSC checks, target-aware diagnostic, and canonical polynomial workflow at that PR revision reported failures. The local evidence is separately identified by main SHA.
- **Hub area #469.** [Focused run 41788241506](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41788241506) succeeded at source `452165960e650cff4262113d46bc5da8dbac89c4`. The broad PSC, target-aware and canonical polynomial workflows at that source reported failures.
- **Carrier #471.** [Focused run 41812558558](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41812558558) succeeded at source `7ca79096b9321a8c6f7f69fe16911145be919939`. This is a bounded address replay.
- **Newer focused runs.** At inspection [#479 run 41832728685](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41832728685), [#481 run 41838796250](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41838796250) and [#482 run 41841725823](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41841725823) were queued. The observed exact-main suite was queued or cancelled. Merge, source-head CI, local replay and journal acceptance are distinct evidence events.
