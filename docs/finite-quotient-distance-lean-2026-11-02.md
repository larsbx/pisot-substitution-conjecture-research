# Conditional finite quotient distances in Lean

Scope: an abstract **finite graph theorem**, using the actual length-indexed
`PscVerif.SelectedRank.Path`. No implementation-refinement or PSC credit.
The canonical executable verifier remains Mojo; this is the deductive layer.

## Accepted finite starting point

PR #447 merged at `9ecc5f8de3411054256d4358795b126c5468be8b`.
Its exact source head `4ec572a60993a0e0d1d9f97ab64257fa61ee209f` passed
[hosted run 41448531108](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/41448531108),
job 125287618392, including native execution, full independent literal
adjacency/distance/lift replay and archived-certificate replay. The downloaded
artifact's checksum manifest verifies, its source revision agrees, and its
entire native stdout and decompressed certificate equal the existing local
packet byte for byte. Original pending receipts are preserved unchanged;
[evidence supplement](../evidence/class-a-finite-hosted-acceptance-2026-11-02/README.md).

## Formal contract

`proof/PscVerif/PscVerif/QuotientDistance.lean` adds sixteen named proofs.
Let G be a finite original graph, Q a finite quotient graph, pi its vertex map,
T the typed actual terminal predicate and U the quotient terminal predicate.
`Refinement` requires all three of the following:

1. Every actual edge u->v projects to pi(u)->pi(v).
2. For **each actual source u** and every quotient edge pi(u)->q there is
   an actual child v with u->v and pi(v)=q. Existence from a single chosen
   representative does not suffice.
3. T(u) iff U(pi(u)); neither direction may be silently dropped.

`path_lift` lifts any quotient path, step by step, from its specified actual
source with its length unchanged. `terminal_path_iff` uses projection and that
lift to identify the **sets of possible terminal path lengths**. Consequently
`no_terminal_path_iff` handles unreachable terminals without assigning a fake
finite distance, and `shortest_iff` identifies shortest lengths whenever a
terminal path exists. No assertion that an arbitrary quotient SCC lifts to a
single original SCC is made.

`ExactWitness` extends the earlier selected-rank `Witness` with every-edge
inequalities r(u)<=r(v)+1. Induction along an arbitrary terminal path gives
r(source)<=length; the selected descending witness supplies a real path of
length r(source). `certified_shortest` therefore proves exact shortest length.
`certified_quotient_distance` combines these contracts to identify the original
and quotient rank labels. It assumes `Refinement`, not just graph counts.

## Calibration and missing-hypothesis controls

- A directed triangle has a genuine two-step selected terminal witness, but
  also a direct one-step terminal edge. `longer_selected_witness` proves the
  former contract; `longer_is_not_exact` refutes `ExactWitness` for that rank.
- Two actual sources have the same quotient name. Source 0 reaches the actual
  terminal, while source 1 has only a self-loop. Edge projection and exact
  terminal membership both hold, and the quotient has a terminal path.
  `one_sided_cannot_lift` proves the every-source lifting premise fails;
  `one_sided_original_trapped` proves the other source has no terminal path.
- `terminal_mismatch_refused` exhibits incompatible terminal sets. Matching
  vertex names cannot be used as an equivalence of typed terminal semantics.

## Native-to-formal boundary

| Lean premise | Existing finite native/Python check | Formal refinement status |
|---|---|---|
| `projects` | full original indexed rows, reversal covariance and quotient construction | assumed by Lean; not derived from executing Mojo |
| `lifts` from every actual source | every quotient edge replayed in both actual orientations with real ordinals/full typed children | assumed by Lean; parser and exact arithmetic not verified in Lean |
| `terminal_iff` | typed full-zero terminals, actual reversal and representative/orbit checks | assumed by Lean; terminalized relation must agree |
| `Witness` | genuine selected occurrence, unit descent and typed zero ranks | abstract witness is an input; native success not imported as an axiom |
| `ExactWitness.bound` | every original and quotient outgoing edge checks the distance inequality | abstract bound is an input; no Boolean acceptance theorem |
| seed-descendant coverage | full literal outgoing enumeration, S18 inclusion and seed reachability for each named specimen | finite executable result; not parameter-uniform or a realized-overlap dictionary |

The new proofs identify precisely what a future verified decoder/checker must
supply. They do **not** turn matching schemas, Python replay, or green CI into
a proof of source-code refinement. Actual occurrence addresses are retained
by the native certificate; the Lean relations abstract over those witnesses.
An occurrence-sensitive refinement must prove those relations denote the
actual terminalized indexed transitions, rather than erase that obligation.

## Replay and trust qualifications

The root module imports `QuotientDistance`, and the generated proof bank
inventories all sixteen new proofs. The normal hosted `lean-proofs` job and
`tools/check_lean.sh` cover them automatically. No dependency pins, vendored
packages or claim statuses change.

Local direct compilation used pinned Lean 4.34.0-rc2 (compiler commit
`6a10ac8c22beadecabdbb0919c2b50214762f91d`). The original startup attempt
failed before elaboration because of the documented numeric procfs lookup.
The existing audited path-only adapter from
`evidence/research-integration-postmerge-2026-11-01/` was reused, with its
negative controls. It redirects only the current process's executable alias
to `/proc/self/exe`; no checker, theorem, pin or library source was changed.
The sixteen direct axiom reports use only standard `propext`/`Quot.sound`
where needed; the projection/lifting/minimum equivalence proofs are axiom-free.
This environment qualification is separate from an unadapted hosted pass.

Normal full replay:

```sh
bash tools/setup_lean.sh
bash tools/check_lean.sh
python -m pytest -q tests/test_proof_bank.py
```

[Pre-implementation stop/go](finite-quotient-lean-stopgo-2026-11-02.md).
The evidence packet records the actual local build/audit outcome separately.
No parameter-uniform X-carrier, all-descendant productive escape, nonunit
realization bridge, BH or general PSC claim follows from this finite interface.
