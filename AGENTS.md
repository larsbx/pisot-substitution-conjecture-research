# Agent implementation policy

## Canonical language

**Mojo is the default and canonical implementation language for executable research code in this repository.**

New algorithms, finite-state constructions, exact arithmetic kernels, census drivers, proof-support instrumentation, and performance-sensitive research tooling should be implemented in `mojo/` first.

Python under `src/psc_research/` is a secondary oracle/prototyping layer. It may be used to:

- cross-check a Mojo implementation with an independently written reference;
- generate small calibration fixtures or counterexamples;
- explore an idea before its contract is stable;
- preserve legacy regression coverage while a module is being ported.

A Python implementation is **not** the source of truth once a corresponding Mojo module exists. New theorem-support code should not merge as Python-only unless there is a documented blocker preventing a correct Mojo implementation.

TLA+ remains the proof-dependency/state-machine model layer and Lean remains the deductive finite-algebra layer. This Mojo-first rule does not replace either formal layer.

## Mojo-first optimization rule

Performance-sensitive code must be designed for Mojo rather than transliterated from Python. Prefer, in this order:

1. **Exploit fixed dimensions.** The standing alphabet-3 kernel should use fixed-size scalar or compact row-major arithmetic for 3-, 9-, and 27-coordinate objects where practical, rather than generic object-heavy containers in inner loops.
2. **Streaming exact algorithms.** Replace combinatorial tuple enumeration with running prefix accumulators when an exact recurrence exists. For example, scattered-subword `N2` and `N3` counts should be accumulated in one pass rather than with `O(n^2)` / `O(n^3)` index loops.
3. **Precompute substitution-local data.** Endpoint maps, image lengths, proper-prefix Parikh vectors, correction alphabets, and other data depending only on `sigma` should be computed once per substitution/census specimen and passed into hot loops.
4. **Reuse storage.** Reuse scratch vectors/buffers and size result storage from known bounds where the Mojo API makes this safe and clear. Avoid repeated temporary list/string construction in graph and census inner loops.
5. **Compact graph/state identities.** Prefer integer indices and compact exact keys after state interning. String serialization is for diagnostics/export, not the preferred long-term key representation for hot BPA lookup paths.
6. **Iterative graph kernels.** Keep SCC, reachability, and closure routines iterative and index-based to avoid recursion overhead and recursion-depth limits.
7. **Fuse passes when it preserves auditability.** For exact censuses, avoid recomputing inflation, factorization, endpoint maps, or Parikh data in independent passes when one verified pass can expose all required outputs.
8. **Fail closed.** Impossible invariant states must abort/raise rather than silently returning empty structures that could be misclassified as mathematical evidence.
9. **Exactness before speed.** Do not replace integer/rational predicates with floating approximations for PIP screening, equality, factorization, rank, or certificate decisions. Optimize the exact algorithm instead.
10. **Benchmark material optimizations.** When changing a hot kernel, add a deterministic correctness regression and, where practical, record the before/after algorithmic complexity or benchmark on a representative corpus slice.

## The census library

Every exhaustive census and catalogue in `mojo/` surveys the same object: the
4,554 primitive irreducible Pisot substitutions on `{0,1,2}` with images of
length at most three. That corpus, and the vocabulary for reporting on it, are
first-class modules rather than something each driver rebuilds:

| Module | Provides |
| --- | --- |
| `mojo/psc/corpus.mojo` | `Specimen`, the deterministic `image_words` order, `pip_corpus`, the shared state cap, the arithmetic regime of the incidence cubic |
| `mojo/psc/histogram.mojo` | bounded exact histogram over integer keys; a key outside its capacity raises |
| `mojo/psc/carrier.mojo` | the two edge facts that classify a recurrent noncoincident SCC (sink, strict carrier), per-state flags, boundary-synchronization lineage, replayable countermodels |
| `mojo/psc/symmetry.mojo` | relabelling and reversal normal forms for words, pairs and substitutions |
| `mojo/psc/defect_degree.mojo` | streaming `N4` and the first scattered-subword defect degree |
| `mojo/psc/degree2_sieve.mojo` | the parity and trace necessary conditions on the incidence cubic |
| `mojo/psc/degree3_taxonomy.mojo` | the degree-3 catalogue taxonomy and its summary lines |

A census driver is then a survey: it walks `pip_corpus()` and folds per-specimen
facts into histograms and counters. A new census should be written that way. Do
not re-enumerate the image words, re-screen the corpus, re-derive sink or strict
-carrier membership by scanning component edges, or hand-roll a histogram line.

The same rule governs scripts. An executable computation belongs in `mojo/` with
a driver and a regression test, not in `scripts/`. What remains under `scripts/`
is the provenance and governance tooling plus the Python census oracles that
cross-check a Mojo census in an independently written language; those are
sanctioned by the oracle policy above. A Python script that is the *only*
implementation of a computation is a defect to be ported, and the ported script
is then deleted rather than kept as a second source of truth.

Exploratory searches are welcome but must be reproducible and must label
themselves: a seeded generator (`mojo/psc/prng.mojo`) or a stated stride, an
explicit resource budget, and output that distinguishes an exhausted budget from
a mathematical verdict (`mojo/psc/bounded_bpa.mojo`). Randomness may never enter
a certificate, a census, or proof-support code.

## Vendored packages

Three logical Mojo packages under `mojo/` are vendored byte-for-byte from the
single `larsbx/finite-math-kernels` monorepo and pinned to one commit by
SHA-256 digest in `vendored.toml`;
`scripts/check_vendored_sync.py` enforces the pins in CI and in
`scripts/verify_all.sh`. Do not patch a vendored file, add a file beside one,
or reintroduce a local copy of what a package provides: change the package
upstream, re-vendor, and re-pin (`scripts/check_vendored_sync.py pin NAME
COMMIT`).

| Package | Upstream | Provides | PSC-side layer |
| --- | --- | --- | --- |
| `mojo/finite_exact/` | `larsbx/finite-math-kernels` | unbounded `BigZ`, normalized `Q`, canonical bytes, closed rational intervals and rank-2 boxes; rejection is sticky | `mojo/psc/exact.mojo`: rejected consumer states raise/abort; Horner helpers, midpoint, diagnostic rendering |
| `mojo/substitution_dynamics/` | `larsbx/finite-math-kernels` | words, substitutions, balanced pairs, automaton, discrepancy over an explicit alphabet | `mojo/psc/words.mojo`, `psc/bpa.mojo`, `psc/swap_discrepancy.mojo` remain thin alphabet-3 views |
| `mojo/finite_linear_algebra/` | `larsbx/finite-math-kernels` | `Mat3`, generic RREF/rank/nullspace over `Q`, rank-three tensors, `W_3`, integer lifts | `mojo/psc/w3.mojo` keeps the printed certificate basis; `psc/exact.mojo` re-exports lifts |

Integer, rational, and rational-interval arithmetic is therefore **not**
implemented in this repository. Do not add a second rational type or a
hard-coded three-letter kernel beside the packages. The PSC binding rows of
the arithmetic specification are in `docs/exact-arithmetic-binding.md`.

## Porting order for the live C4 program

The current C4 recognizability/factorization work is being migrated to this policy. The preferred order is:

1. shared word/prefix and BPA primitives in `mojo/psc/`;
2. multi-level prefix ancestry and legal-context/tower primitives;
3. derived substitution/address and orientation-aware birth events;
4. relative hierarchy-offset state/transducer;
5. exact corpus instrumentation using those Mojo modules.

Python copies may remain as independent reference oracles during migration, but new results should cite the Mojo implementation as canonical.

## Review gate

### Targeted literature stop/go check

Before implementing a new theorem-facing diagnostic, testing a proposed
universal invariant, or promoting a proof lemma, perform a small targeted
literature review first. Its purpose is to avoid spending computation or proof
effort on a known construction, a known counterexample, or a route whose
hypotheses do not match the standing PIP regime.

Keep the check proportional: normally inspect three to six primary sources
covering (1) the closest known construction, (2) the strongest relevant
theorem, and (3) known hypothesis/counterexample boundaries. Record a short
stop/go note in `docs/` containing:

- the exact proposed claim or experiment;
- prior art and the terminology used in the field;
- hypotheses that transfer and those that do not;
- known negative controls or counterexamples;
- the resulting decision: stop, redirect, or proceed with a narrowed target.

Only after that decision should new theorem-facing tests or proof code be
written. Pure regression repairs for an already reviewed contract do not need
a new review. If the review shows that a proposed identity is standard, cite
it and restrict novelty claims to the actual new specialization, certificate,
or theorem.

For new executable mathematical machinery, a PR should normally contain or depend on:

- a canonical Mojo implementation;
- Mojo regression coverage for the theorem/invariant contract;
- explicit counter-calibrations for known overstrong variants;
- Python oracle coverage only when it adds independent value;
- no claim beyond what the exact executable or formal proof actually establishes.
