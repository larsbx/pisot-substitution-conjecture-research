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

## Vendored packages

Four Mojo packages under `mojo/` are vendored byte-for-byte from their own
repositories and pinned by commit and SHA-256 digest in `vendored.toml`;
`scripts/check_vendored_sync.py` enforces the pins in CI and in
`scripts/verify_all.sh`. Do not patch a vendored file, add a file beside one,
or reintroduce a local copy of what a package provides: change the package
upstream, re-vendor, and re-pin (`scripts/check_vendored_sync.py pin NAME
COMMIT`).

| Package | Upstream | Provides | PSC-side layer |
| --- | --- | --- | --- |
| `mojo/finite_exact/` | `larsbx/finite_exact` | unbounded `BigZ`, normalized `Q`, canonical bytes; rejection is a sticky flag, never an exception | `mojo/psc/exact.mojo`: a rejected enclosure raises, a rejected scalar in integer-seeded polynomial arithmetic aborts; Horner helpers, midpoint, diagnostic rendering |
| `mojo/interval_q/` | `larsbx/interval_q` | closed rational intervals `IQ`, rank-2 boxes `ComplexIQ`, three-valued sign | same module; Perron-root enclosures and overlap margins in `psc/` |
| `mojo/substitution_dynamics/` | `larsbx/substitution_dynamics` | words, substitutions, balanced pairs, automaton, discrepancy over an explicit alphabet, validated once at `Substitution.checked` | `mojo/psc/words.mojo`, `psc/bpa.mojo`, `psc/swap_discrepancy.mojo` are thin alphabet-3 views and must stay thin: general mechanics go upstream, conjecture-specific predicates stay in `psc/` |
| `mojo/finite_linear_algebra/` | `larsbx/finite_linear_algebra` | `Mat3`, generic RREF/rank/nullspace over `Q`, rank-three tensors, the shuffle kernel `W_3`, integer lifts | `mojo/psc/w3.mojo` keeps the printed certificate basis; `psc/exact.mojo` re-exports the lifts |

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
