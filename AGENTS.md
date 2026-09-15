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

## Exact arithmetic authority

Integer, rational, and rational-interval arithmetic is **not** implemented in
this repository. `mojo/finite_exact/` is a vendored copy of
`src/bigint_z.mojo`, `src/rat_q.mojo`, and `src/interval_q.mojo` from
`larsbx/NLAP-JT`, identical to the upstream sources except for the
package-qualified intra-package import lines, pinned in
`mojo/finite_exact/UPSTREAM.md`, and enforced by
`scripts/check_finite_exact_sync.py` in CI (which reverses the import rewrite
before comparing digests). Do not add a second rational type,
patch the vendored files, or reintroduce fixed-width rational arithmetic:
change upstream, then re-vendor. PSC-specific conventions over that package
(raise or abort on a rejected value, integer lifts, Horner helpers, diagnostic
rendering) live in `mojo/psc/exact.mojo` and nowhere else.

## Substitution-dynamics package

Words, substitutions, balanced pairs, the balanced-pair automaton, and
swap-walk discrepancy live in `mojo/substitution_dynamics/` over an explicit
alphabet, validated once at `Substitution.checked`. `mojo/psc/words.mojo`,
`mojo/psc/bpa.mojo`, and `mojo/psc/swap_discrepancy.mojo` are alphabet-3 views
of that package and must stay thin: add general mechanics to the package and
conjecture-specific predicates to `psc/`. Do not reintroduce a hard-coded
three-letter kernel beside it. See `mojo/substitution_dynamics/README.md`.

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
