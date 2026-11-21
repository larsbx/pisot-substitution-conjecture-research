# Nonemptiness of the legal hull: source decision

**Status:** Source decision for gap 5 of the [hull note](c4-tiling-hull-realization-2026-11-19.md#non-claims-and-remaining-gaps):
"nonemptiness for PIP3 members is not instantiated". Starting revision:
`main@8bbc05b8`. No governed claim changes.

## Exact target

Prove `Nonempty S.Hull` for every `LengthSubst α` on a finite nonempty alphabet with `1 < β`.
Then specialize it to `PIP3` and to every member of the Lean census
([census note](c4-pisot-census-2026-11-19.md)). The proof must supply the three seed
hypotheses of `hull_nonempty_of_seed`: tiling of an interval around `0`, growth under a
positive power of inflation, and legality.

## Sources

| Source | Use and boundary |
| --- | --- |
| Baake–Grimm, *Aperiodic Order* vol. 1 (2013), §4.2: legal seeds and fixed points of a power of a primitive substitution | The classical seed `b.a` with `σᵏ(a)` beginning with `a`, `σᵏ(b)` ending with `b`, `ba` legal. Bibliographic only; **not re-opened** in this session. Nothing is imported from it. |
| Queffélec, *Substitution Dynamical Systems* (2nd ed., 2010), ch. 5 | Same construction for primitive substitutions. Bibliographic only; **not re-opened**. |
| Barge–Diamond, [Cohomology in one-dimensional substitution tiling spaces](https://arxiv.org/pdf/math/0702669), §2 | Legal bi-infinite tilings as in the hull definition (already used by the hull note). |

## Transfer

- The classical argument assumes primitivity to obtain a legal two-letter word. Here legality
  is relative to supertiles of *any* letter, so it is enough that some image has two
  letters. With `1 < β` and positive lengths that is forced: if every image were a single
  letter, lengths would multiply by `β` around a cycle of the first-letter map.
- The periodic pair is obtained from one eventually periodic orbit of
  `(x, y) ↦ (last σ(x), first σ(y))` on `α × α`. This is pigeonhole on a finite type, and
  no factorial-power idempotent is needed.
- No external theorem enters. The result is unconditional on the stated hypotheses.

## Decision

**Proceed.** Prove it in a new module `PeriodicPartnerHullNonempty`. Apply it to
`PIP3`, to the census through `PeriodicPartnerSpectralCensus.census`, and to Tribonacci.
