# C4 actual ordered strict-birth atlas — 2026-11-02

**Status:** new canonical finite word-level instrument with exact negative
control and a conditional complete-event soundness statement. **Not** a proof
of C4, G1, A1′, BH, PDS or PSC.

**Baseline:** `main@76e4058e0ee8a94178c5b32e4512e119376a5234`,
which includes merged #450, the [bilateral-born cut theorem and
controls](c4-bilateral-birth-rigidity-2026-11-02.md). The historical
[Issue #9](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/9)
closure is research-track closure only. A **supplied finite strict
child-closed** component is an additional hypothesis: G1 extraction
from global nonproductivity remains separate and open.

## Stop/go and prior sources

Proceed with a **complete literal all-child atlas** rather than another
synthetic packet quotient, reusing the already checked
`psc.derived_system.build_derived_system`,
`psc.bpa.coincidence_boundaries`, and
`psc.c4_cut_alignment.classify_irreducible_birth`. These are exactly
the interfaces isolated by the existing
[C4 good-edge bridge](c4-good-edge-system-bridge.md),
[target-aware diagnostic](target-aware-bpa-diagnostic-2026-10-02.md)
and [ordered-hub negative](c4-ordered-hub-offset-negative-2026-10-06.md).
For terminology/attribution use the already recorded
[Martensen/Barge–Diamond/Durand–Leroy literature
stop/go](c4-ordered-hub-literature-gate-2026-10-06.md).
Their results do not upgrade a finite local candidate to C4.

## Exact input/complete-event contract

Given a nonempty finite list `C` of normalized irreducible,
noncoincident balanced states and a nonerasing ternary substitution
`sigma`, the canonical `strict_birth_atlas` first invokes the
**actual-word** derived-system constructor. It rejects a diagonal
child, an omitted noncoincident child, reducible/unbalanced state or
duplicate normalized state. It independently inflates each parent
and checks the complete zero-return count against its derived child
word, including the *order* and occurrence multiplicity.

For every interior boundary after ordinal `k-1` and before ordinal
`k`, the atlas records:

- parent ID, **ordered right-child ordinal** and physical cut;
- immediately left and right normalized child IDs and raw
  orientation signs;
- literal top/bottom source occurrence indices and proper
  within-image digits;
- source prefix Parikh defect `E`, exact local forcing `c`,
  checked by `M E+c=0` and integer-image membership;
- actual left-adjacent and right-adjacent letter pairs, with
  their respective suffix/prefix eventual-equality checks.

The routine **refuses** any supposedly strict system whose literal
left or right newborn endpoint pair eventually synchronizes.
This refusal follows from the complete strict-child assumption:
a synchronizing adjacent endpoint would produce a coincidence in
a later child inflation, contradicting permanent strict closure.
This is a *consistency check*, not an algorithm certifying that an
arbitrary input substitution is PIP or that a strict PIP component
exists.

### Conditional event completeness

Under a successfully validated, **fully** strict input system,
every actual one-step interior zero return of every supplied state
appears exactly once, with its true ordered left/right child IDs,
physical orientation and literal ancestry fields.

**Proof.** Actual zero returns of `sigma(T)` partition the entire
inflated pair into consecutive irreducible child blocks. The
constructor checks precisely these blocks and their normalized IDs.
There is one interior zero-return position between each consecutive
pair of blocks. The atlas traverses the complete ordered cut list,
reconstructs each physical cut independently and records the two
neighboring factor IDs. Thus every such event is included exactly
once. No statement about arbitrarily deep *legal towers* or a
globally extracted strict component follows. QED.

A per-call cap bounds the number of recorded events. Exceeding it
raises, rather than returning an apparently empty/no-birth result.
Mathematical completeness holds **conditional** on an uncapped
successful execution, with the input's fully validated factorization.
Machine-integer image and parent-length budgets are inherited from
the cut classifier. No floating point or independent unimodularity
assumption is introduced.

## Golden strict control: 12 complete word events

Use the existing **primitive full-rank but non-PIP** strict fixture
`sigma=10/102/211`, incidence polynomial
`(x-1)(x²-2x-2)`. It has genuine four-state closed derived
system `S0,S1,S2,S3` with ordered child rows

```text
S0 -> [S2]
S1 -> [S3]
S2 -> [S2,S0,S0,S1,S0]
S3 -> [S2,S0,S0,S1,S0,S1,S0,S1,S0]
```

The atlas must report **12** strict literal newborn events:
zero from `S0,S1`, four from `S2`, eight from `S3`.
Every event has at least one nonzero within-image digit and neither
adjacent endpoint pair eventually synchronizes.

Two independently pinned events on `S2`:

| right ordinal | cut | left/right child | top source/digit | bottom source/digit | E | c |
| ---: | ---: | --- | --- | --- | --- | --- |
| 1 | 8 | S2/S0 | (3,0) | (2,2) | (1,0,0) | (-1,-1,0) |
| 3 | 14 | S0/S1 | (5,1) | (5,0) | (1,-1,0) | (0,0,1) |

The last event of `S3` is at right ordinal 8 and cut 35,
with top source/digit `(13,0)` and bottom `(12,2)`.
These are source-word positions, not quotient-state-only labels.

**Negative layers:** the productive recurrent Tribonacci
`(01,10)` support is rejected at strict-system construction
because its true child word contains diagonals. The older primitive
non-Pisot two-state strict fixture is singular and rejected by
the full-rank cut classifier. A truncated three-state subset of
the four-state control is rejected for missing children. A cap
below 12 events raises rather than issuing a false complete record.

This control is **not** a PIP counterexample; it exists specifically
to show that primitive expansion, incidence full rank, and exact
ordered-word geometry are *insufficient* without the irreducible
Pisot hypothesis.

## All-child hub-bit flatness: a stronger failed shortcut

The same primitive, full-rank, **non-PIP** four-state strict fixture
`sigma=10/102/211` rules out another tempting simplification:

> **Retired candidate (false without irreducible Pisot):**
> strict all-child closure, integral newborn-source ancestry and a
> *constant ordered hub-residual phase on every actual occurrence*
> force an interior synchronizing cut.

This fixture's prefix endpoint map is `h=(1,1,2)`. For its actual
complete ordered derived words, every raw child has orientation sign
`+1`. Every canonical first pair is `(1,2)`. The two candidate
good-edge placements `{0,1}` (hub 2) and `{0,2}` (hub 1)
both survive the finite first-child compatibility mask, which is
`0b011`. This mask is a **necessary compatibility mask**, not a
certificate that either edge is eventually coincident (the fixture
does not meet Barge–Diamond's Pisot hypothesis).

For **each** hub choice, the normalized-state hub side is constant
across the entire component (top for hub 1, bottom for hub 2). Hence
the existing gauge identity
`r_h(parent->child)=b+x_h(parent)+x_h(child) (mod 2)`
gives the *full ordered* child-residual words

```text
S0: [0]
S1: [0]
S2: [0,0,0,0,0]
S3: [0,0,0,0,0,0,0,0,0].
```

These are all **actual** child occurrences, not the selected first
child or a six-state abstract letter-pair inflation. Nevertheless,
all 12 actual interior newborn cuts remain right/left endpoint
nonsynchronizing. All literal Parikh/residue checks and actual strict
child closure continue to hold.

There is an **exact algebraic explanation** why this concrete
full-rank primitive example does not meet the irreducible-PIP
Parikh-intertwiner constraint. Write `P_C` for the three-by-four
matrix of the balanced state Parikh columns and `N_C` for the
four-by-four actual derived child-incidence matrix:

```text
       [1 1 2 4]               [0 0 3 5]
P_C =  [1 3 4 6]       N_C =   [0 0 1 3]
       [1 1 2 4]               [1 0 1 1]
                               [0 1 0 0]

M = [1 1 0; 1 1 2; 0 1 1],
P_C N_C = M P_C = [2 4 6 10; 4 6 10 18; 2 4 6 10].
```

The first and third Parikh rows agree; a top-left two-by-two
minor is `2`. Thus **rank_Q(P_C)=2**, exactly (not a
numerical approximation). In particular the invariant rational
subspace `{v: v_0=v_2}` is proper. The incidence characteristic
polynomials obey

```text
chi_M(t)   = (t-1)(t^2-2t-2)
chi_N_C(t) = (t-1)(t+2)(t^2-2t-2).
```

The identity is the already proved
[Parikh intertwiner](c4-parikh-intertwiner.md), not a new
original theorem. That result forces **rank_Q(P_C)=3**
whenever the ternary `chi_M` is irreducible. Consequently this
particular flat-word strict countermodel fails *two exact necessary
tests* for a genuine PIP strict SCC: irreducibility of `chi_M`
and the resulting Parikh-rank-three condition. This identifies
a mathematical obstruction—not merely the label `non-PIP`.
It does **not** establish that rank three together with flat
hub words would force synchronization in every possible
irreducible PIP system; that implication remains unproved.

The canonical test and independent word oracle now recompute the
three-by-four Parikh columns, complete occurrence-incidence
matrix, exact intertwining and the nonzero rank-two minor.

This observation strengthens the earlier singular non-Pisot control:
the complete **ordered** hub bit word may be perfectly phase-flat
even in a primitive nonsingular strictly nonproductive component.
Any proof claiming that phase-flatness plus word-realizable
newborn cuts suffices must use a genuinely stronger **irreducible
Pisot/spectral or recognizability** hypothesis and show its
transmission to the actual ordered words. Simply upgrading the
first-child phase to all child occurrences, *even when verified
true in a given component*, does not supply C4.

Canonical regression:
`kernel/tests/test_c4_strict_birth_atlas.mojo` now checks the two
hub choices against `candidate_good_edge_mask`,
`build_hub_cocycle`, the actual full child words and exact Perron
phase gauge invariance. Independent
`tests/test_c4_cut_alignment_oracle.py` reconstructs every
raw child word, orientation and hub bit without using the canonical
gauge module. This is a **negative-control finding**, not a new
PIP counterexample or an independently reviewed proof of C4.

## Verification / scope

- Canonical Mojo: `kernel/psc/c4_strict_birth_atlas.mojo`.
- Auto-discovered Mojo regression:
  `kernel/tests/test_c4_strict_birth_atlas.mojo`.
- Independent standard-library Python:
  `tests/test_c4_cut_alignment_oracle.py` now reconstructs all
  twelve events without calling the Mojo module.
- Replay from `kernel/`:
  `mojo run -I . tests/test_c4_strict_birth_atlas.mojo`.
- Replay from repository root:
  `python -m pytest -q tests/test_c4_cut_alignment_oracle.py`.

At authoring, these **new exact-head hosted workflows have not yet
completed**. The enumerated data above were independently reconstructed
in exact local Python; the canonical Mojo implementation and
test still require a hosted compiler/test receipt. Original
#450's Mojo compile failure had a separate exact error:
non-ImplicitlyCopyable `Pair` list literals. PR #456 fixes that
issue on an independent branch; it is not silently assumed merged
here. If the full suite is red from that baseline, distinguish
this pre-existing failure from the new atlas's own compilation/logic.

Independent human review remains final validation debt; never
describe this note as reviewed or machine-certified before
the relevant exact-revision workflow passes.

## Next proof target

The atlas makes the word-level domain checkable, but supplies no
**uniform irreducible-Pisot mechanism** that forces at least one
event in `Sync_+` or `Sync_-`. The next theorem must use
the irreducible Pisot spectrum and the actual **ordered hub-residual
word** over all child boundaries, with legal tower/ancestry
alignment proved where invoked.

Do **not** infer global G1 from this given-component C4 interface,
turn a productive packet SCC into a strict one, use the invalid
predecessor-contraction shortcut, or promote finite accepted records
to a universal result. BH #139 and A1′ #138 remain separately open.
