# C4 on the standing corpus, and the C4 node as a conditional theorem — 2026-11-05

**Status:** finite-domain theorem on the exact 4,554-member corpus (claim
`C4StandingCorpus`, guarded by `kernel/tests/test_c4_standing_corpus.mojo`),
and a re-filing of the ledger node `C4` from an open premise to a repository
theorem conditional on the aligned lemma A (`UniversalAlignedCoincidence`,
[issue #138](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/138))
through the new node `C4FromStrongCoincidence`. General C4 remains open. No
pure discrete spectrum is decided. Human review pending.
[Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).

## 1. What C4 is

The manuscript (`manuscripts/PSC_balanced_pair_state_2026-09-13.tex`) calls a
finite closed nonproductive recurrent noncoincident SCC of the balanced-pair
automaton a **strict component**, and defines for a strict component `𝒞`:

- **C2**: some `T ∈ 𝒞` and `n ≥ 1` give a zero return of `σⁿ(T)` with right
  pair in `Sync₊` or left pair in `Sync₋`;
- **C3-local**: some `T ∈ 𝒞` gives an interior zero return of `σ(T)` with right
  pair in `Sync₊` or left pair in `Sync₋`.

C3-local ⇒ C2 ⇒ contradiction with nonproductivity (manuscript, one-way
chain). **C4** is the program of proving C3-local for every strict component
(Open Problem `prob:C4`, "uniform alignment"); in the ledger it is the premise
of `C3Local → C2 → SCCProducer → PDS`. Since C4 quantifies over strict
components, it holds vacuously wherever none exists.

A strict component is exactly a strongly connected *strict system* in the
sense of the [cut-pair note](c4-cut-pair-productivity-2026-11-04.md): finite,
strictly child-closed, noncoincident.

## 2. The reduction (repository-proved)

**Theorem A(4)** of the cut-pair note: every first-letter pair of a strict
system has no left strong-coincidence witness. Its proof is three lines: a
witness `σⁿ(c) = PxQ`, `σⁿ(c′) = P′xQ′`, `p(P) = p(P′)` makes `|P|` and
`|P| + 1` balanced cuts of `σⁿ(u,v)` for a state with first letters `c, c′`,
and the factor between them is the coincident `(x,x)`, which strict closure
puts inside the system. Hence:

> **C4FromStrongCoincidence.** If every pair of distinct letters of `σ` is
> left strongly coincident, then `σ` has no strict component, and C3-local
> holds for every strict component vacuously.

The hypothesis is the aligned lemma A of #138 ("every pair of distinct letters
is eventually prefix coincident"). So the implication `C4 ⟸ A` is a theorem,
and the ledger now records `C4` as a conditional theorem with dependencies
`C4FromStrongCoincidence` and `UniversalAlignedCoincidence`. The dependents
`C3Local` and `C2` trace their open premise to #138 instead of to C4;
`SCCProducer` and `PDS` keep their other open premises (G1).

This is a re-filing of a proved implication. It does not promote #138, and it
does not shorten the route to PDS: #138 was already a premise of
`TwoObstructionCompletion`.

## 3. The finite-domain theorem

> **C4StandingCorpus.** For each of the 4,554 primitive irreducible Pisot
> substitutions on `{0,1,2}` with images of length at most three, no strict
> component exists; C3-local, hence C2, holds vacuously for every one of them.

*Proof.* The exact affine coincidence automaton of `psc.coincidence_formula`
decides, for each specimen and each of its three letter pairs, the least level
of a left strong-coincidence witness, returning `−1` only as a decided
negative (the exploration is finite by the Pisot property). On the corpus it
returns a witness for all `13,662` pairs: `7,302` pairs are merged by the
first-letter map (a trivial witness at the left end of `σⁿ`), and the `6,360`
residual pairs, spread over `2,658` specimens, have least levels

```text
2:828  3:1956  4:1812  5:1200  6:384  7:132  8:18  12:6  13:6  14:12  15:6
```

(the deepest, level 15, on the reversal class of `1/2/01`). Theorem A(4)
finishes. ∎

This is the same computation as `kernel/strong_coincidence_census.mojo`
(`SC_all failures: 0`), now bound to the C4 conclusion and guarded by a
regression that re-decides every pair. The `3,012` specimens whose prefix or
suffix map is eventually constant are covered twice over: there every balanced
pair is productive outright (manuscript, Theorem "Global endpoint
synchronization"; the endpoint-collapse stratum of the
[cut-attractor note](c4-cut-attractor-window-2026-11-05.md)).

## 4. Why this is where C4 finishes for now

By Proposition 3 of the cut-attractor note, for any primitive `σ`,

```text
C4(σ)  ⟺  bounded-gap A1′ for every power of σ,
```

and by Proposition 2, `A1′` for every PIP substitution is equivalent to
`SC_all` for every PIP substitution. So the only content of C4 beyond #138 is
the bounded-gap slack, and the six audited routes of 2026-11-05 show that
slack buys nothing at this altitude: Lemma F and Lemma G convert it into an
open overlap of two subtiles on a hub pair, and the only known contradiction
to an open overlap is strong coincidence on that pair. At coincidence rank 2
the open overlap is *equivalent* to a strict component (Proposition R,
conditional), and the [`dim H¹` census](c4-h1-census-2026-11-05.md) confines
coincidence rank 2 to 492 unimodular specimens, on all of which the corpus
theorem above already applies.

The next open quantifier is therefore #138 itself, in its weakest useful form:
for unit PIP `σ` with `cr(σ) = 2` and every letter pair without a left
strong-coincidence witness, `int(R_c ∩ R_c′) = ∅`.

## 5. Replay

```sh
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_standing_corpus.mojo)
(cd kernel && pixi run --locked mojo run -I . strong_coincidence_census.mojo)
python3 tools/make_ledger.py --check
PYTHONPATH=tools python3 -m claim_governance.cli --root .
```

The regression re-decides all `13,662` pairs (about 16 s), pins the residual
counts and the level histogram, and declares `require_claim("C4StandingCorpus")`
and `require_claim("C4FromStrongCoincidence")`. The reducible strict control
`10/102/211` lies outside the domain: the exact automaton needs an irreducible
cubic, and its unwitnessed cut pair `{1,2}` is pinned by the bounded search of
`test_c4_cut_attractor.mojo`.

## 6. Non-claims

General C4, BH (#139), A1′ (#138), G1, PSC: open. No specimen's spectrum is
decided here (that is `BoundedPureDiscreteSpectrum`'s business, by other
means). The conditional status of `C4` is the status of the implication; the
premise #138 is unchanged. Nothing in this note is a universal statement about
substitutions outside the 4,554-member domain except the implication of §2.
