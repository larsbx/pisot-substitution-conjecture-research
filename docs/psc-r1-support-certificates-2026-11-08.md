# R1 support-local certificates — 2026-11-08

**Baseline:** `main@14b735e664368729f01a5fae4947cfd166236a1c`, including the
merged #516 productivity correction, #517 source-return repair, and #518
append-only ledger correction. **Status:** new formal checker interfaces;
not a PSC/C4/BH/A1′/G1 result. No claim classification changes or automatic merge.

## Work shown

### Assumptions and hypotheses

Let `actual(s)` be the **complete ordered literal child-factor list**, including
coincidences, repeated occurrences, raw side orientations and exits. Let
`stateOK(s)` independently recognize the intended source-state domain, and let
`target(s)` recognize a one-letter diagonal, not merely a common vertex or an
equal letter at a nonzero residual. These are the source specification; they
are not unauthenticated flags supplied by a proposed certificate.

A finite packet supplies `decode : Fin n -> Raw`, child rows of indices, a
selected-support mask and/or natural-number ranks. Literal list equality
`map decode (rows i) = actual(decode i)` is stronger than equality of edge
sets: order and multiplicity must match. Injectivity of `decode` is not needed
for the stated semantic conclusions; aliased indices cannot invent a raw
successor because every accepted row is compared with the raw list. Canonical
Mojo packet admission may impose additional duplicate-normalization rules.

### Derivation / reduction

**Negative certificate.** `strictCheck` accepts only a nonempty selected set,
source-valid states, exact full literal rows for every selected state, no
diagonals there, and closure of **every** child in those rows. The Lean proof
maps that mask to a set of raw source states and inducts on arbitrary-length
raw child paths. Every accepted member is nonproductive. This proves closure
and nonproductivity, not recurrence/strong connectivity or PIP hypotheses.
An empty support, an omitted exit, reordered occurrences and altered
multiplicity are rejected. No root outside this support enters the proof.

**Positive certificate.** `rankCheck` compares **every** represented row with
its complete literal source row. Each nontarget state must have at least one
actual successor of smaller natural-number rank. Strong induction on that
rank proves productivity of each represented state. Complete row coverage
then proves productivity of **every raw descendant** of any represented
state. This is the repaired all-descendants implication: it follows from an
all-state certificate plus exact source coverage, not from root productivity.
Other edges may form cycles; the result is existential reachability, not
termination of every walk or an all-edge strict ranking.

**Extraction firewall.** The elementary equivalence between nonproductivity
and membership in a child-closed target-free set holds for arbitrary graphs,
but its witness may be infinite. The new Lean theorem deliberately does not
claim that arbitrary BPA nonproductivity yields a finite strict component.
That remains the separate G1/extraction obligation. Neither checker generates
the required packet or proves its existence for all Pisot substitutions.

### Evidence and replay

- `proof/psc_routes/R1SupportCertificate.lean`: twelve generic theorems,
  including arbitrary-path strict-support soundness and all-raw-descendant
  productivity under a complete finite rank certificate.
- `proof/psc_routes/R1SupportFixtures.lean`: thirteen concrete theorem
  declarations binding both checkers to independently recomputed literal
  factorization rows. The binary negative fixture reuses the already
  accepted `R1ProductivityScope` source specification; it is not silently
  replaced by an invented graph.
- `proof/quint/PscR1SupportCertificate.qnt`: twelve deterministic tests that
  reconstruct both source substitutions and every balanced cut independently.
- `.github/workflows/psc-r1-support-certificates.yml`: exact-head checkout,
  repository-pinned Lean/Mathlib, pinned Quint 0.33.1 TypeScript backend,
  complete declaration/axiom inventories, explicit expected test names,
  positive test counts, and mutations that must fail for the intended reason.

The local dependency-free fixture oracle independently reconstructed all
ordered rows. It exhausted all **32** support masks on the five-state binary
fixture (exactly `{plus,minus}` accepted), all **16** masks on the four-state
positive fixture (none accepted as strict), and all **256** rank assignments
with coordinates in `{0,1,2,3}` on the latter (56 accepted). It checked omitted
exits, raw-order and multiplicity mutations and malformed finite packets.
This is exact **finite fixture replay**, not Lean or Quint execution and not
an exhaustive substitution census. The attached replay receipt hashes the
formal source files. No local Lean/Quint runtime receipt is claimed: these
executables were unavailable in this session, and the newest hosted workflow
must be inspected separately. A prior green run or a source declaration count
is not acceptance of these new modules.

### Negative controls

For the literal binary substitution `0->01, 1->10`, the legal irreducible
root `001/100` has the ordered children

```
01/10, 0/0, 1/1, 10/01.
```

Its off-diagonal class `{01/10,10/01}` is closed and nonproductive. Deleting the
two diagonal exits makes a graph-only test wrongly declare the support that
also includes the root strict; exact literal-row comparison rejects that
packet. Reversing or repeating a child occurrence is rejected even if the
underlying successor set is unchanged. This is the established reducible-
incidence control, not a PSC counterexample.

For the literal positive source `0->01, 1->0`, the complete raw child rows are

```
plus  = 01/10 -> [0/0, minus]
minus = 10/01 -> [0/0, plus]
0/0             -> [0/0, 1/1]
1/1             -> [0/0].
```

The ranks `(1,1,0,0)` certify productivity of the whole finite carrier and all
its descendants. Nevertheless, the `plus -> minus -> plus` walk avoids the
diagonal indefinitely. Thus the certificate must require ONE decreasing
successor, not every edge to decrease, and its conclusion must remain
existential. The Quint mutation replacing `exists` with `forall` must fail
the positive test. A second mutation omitting literal-row coverage must fail
the hidden-diagonal-exit test. This small source does not supply a general
three-letter strict-support theorem, even though its own rows are complete.

### Non-claims / remaining gaps

There is no new finite support extractor, no universal SCC-productivity
result, no new bounded-gap theorem and no source-ordered ancestry refinement
for #514. The live proof boundary remains constructing/certifying the
**actual required support** for the general PIP route and proving a target
path from inside it. The corrected shared ledger and all historical findings
are preserved. Human validation is post-PSC; machine checks and explicit
hypotheses remain immediate requirements.

## Targeted prior-art and dependency decision

**Proceed as formal refinement, not a new mathematical mechanism.** The
backward-productivity and sink-component reasoning is already recorded in
`psc-r1-productivity-impact-2026-11-08.md`; the accepted binary counterexample
and Tribonacci common-prefix theorem are in #516, with the ledger correction
in #518. The canonical Mojo admission surface already rejects incomplete
strict supports (`kernel/psc/derived_system.mojo`,
`kernel/psc/c4_strict_birth_atlas.mojo`), as documented in
`c4-strict-birth-atlas-2026-11-02.md`. The existential/all-walk distinction and
complete graph premise predate this work in
`c4-ordered-word-completion-interface-2026-11-02.md` §3 and
`class-a-reversal-native-2026-11-02.md`.

The standard reachability/ranking argument uses no Pisot theorem. Sirvent–
Solomyak (2002), DOI `10.4153/CMB-2002-062-3`, remains the literature bridge
for the balanced-pair spectrum route, not a justification for forward
productivity or for finite extraction. No new novelty assertion is made.
This work isolates the soundness obligations so a future canonical Mojo
packet producer can refine them without adding a Python-only research
implementation. Quantitative density-one arguments in the manuscript and
the independent R2/R3/R4 routes remain separate, unchanged dependencies.


## Decidability repair follow-up

The baseline Lean source-compilation failure and its computable instance repair
are documented in [the repair acceptance note](psc-r1-decidability-repair-2026-11-08.md).
The original mathematical conditions and all theorem statements are preserved.
Use the PR exact-revision receipt table for current hosted acceptance; the
historical finite oracle above is not a Lean kernel receipt.
