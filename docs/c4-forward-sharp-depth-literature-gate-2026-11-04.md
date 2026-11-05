# Literature gate: sharp all-pairs coincidence depth and prefix-satellite lifting — 2026-11-04

**Status:** stop/go note (AGENTS.md "Targeted literature stop/go check") for
the Theorem, Lemma and Corollary of
[the forward-family sharp-depth note](c4-forward-run-family-sharp-depth-2026-11-04.md)
(PR #483). It moves no governed claim status.

## Proposed claim

For the forward run family `sigma(0)=01`, `sigma(1)=1^a 2 1^b`,
`sigma(2)=012` (`a,b >= 0`, `a+b >= 1`):

1. the least generation `D(a,b)` with a simultaneous three-letter
   equal-Parikh-prefix / common-next-letter cut is 2, 2, 3, 3, 4 on the five
   chambers `a=0`; `a=1,b>=1`; `a=1,b=0`; `a>=2,b>=1`; `a>=2,b=0`;
2. the pairwise minimum depths of `({0,1},{0,2},{1,2})` are `(D,1,D)`, so the
   earliest all-pairs strong-coincidence generation is exactly `D`;
3. (general, any nonerasing substitution) if `tau(k)=tau(i)W` literally, then
   `tau^n(k)=tau^n(i)tau^(n-1)(W)`, so every `{i,j}` witness at depth `n` is a
   simultaneous `{i,j,k}` witness at the same cut and depth; on three letters
   one `{i,j}` witness then gives all-pairs strong coincidence by generation
   `n` (the prefix-satellite sufficient criterion).

## Prior art and terminology

1. **P. Arnoux, S. Ito**, *Pisot substitutions and Rauzy fractals*, Bull.
   Belg. Math. Soc. Simon Stevin 8 (2001), 181–207. Defines the (positive)
   strong coincidence condition for a pair `i,j`: some `n` and a decomposition
   with equal prefix abelianization and equal next letter. Under strong
   coincidence for all pairs (unimodular, irreducible Pisot) the Rauzy subtiles
   are measure-disjoint (their Thm 2). This is the "pairwise strong
   coincidence" used here; the depth `n` is not optimized there.
2. **M. Barge, B. Diamond**, *Coincidence for substitutions of Pisot type*,
   Bull. Soc. Math. France 130 (2002), 619–626. Every Pisot substitution has a
   strongly coincident pair of distinct letters; for two letters this is the
   full strong coincidence condition. On three letters the all-pairs condition
   is the open Arnoux–Ito question.
3. **F. M. Dekking**, *The spectrum of dynamical systems arising from
   substitutions of constant length*, Z. Wahrscheinlichkeitstheorie verw.
   Gebiete 41 (1978), 221–239. Column coincidence in the constant-length case;
   the ancestor of the coincidence terminology.
4. **V. F. Sirvent, B. Solomyak**, *Pure discrete spectrum for one-dimensional
   substitution systems of Pisot type*, Canad. Math. Bull. 45 (2002), 697–710.
   Balanced-pair algorithm and its termination-with-coincidence equivalences
   (Thms 5.1, 5.6).
5. **S. Akiyama, M. Barge, V. Berthé, J.-Y. Lee, A. Siegel**, *On the Pisot
   substitution conjecture*, in *Mathematics of Aperiodic Order*, Progress in
   Mathematics 309 (2015), 33–72. Survey: pure discrete spectrum ⇔ balanced
   pair algorithm terminating with coincidence (Thm 5.3); all-pairs strong
   coincidence listed as open in general.

In-repository prior art: **Lemma T (prefix transfer)**,
[A1′ note §3c](p1a-a1-prime-2026-10-05.md) and side-notes ledger 2026-10-06:
`sigma^(n+1)(i)` begins with `sigma^n(h(i))`, carrying a coincidence from level
`n` to level `n+1` backwards along the first-letter pair map. The
prefix-satellite lemma is the same multiplicativity argument applied to a full
image prefix `tau(k)=tau(i)W`, which keeps the **same** level and cut.

## Hypotheses that transfer

- The definition of a strong-coincidence witness (equal Parikh prefix, equal
  next letter) is exactly Arnoux–Ito's positive (prefix) condition; the
  family's Pisot/irreducible/primitive status is proved in merged #479.
- The prefix-satellite lemma uses only that substitutions are monoid
  morphisms; no Pisot, unimodular or BPA-finiteness hypothesis.
- The "no nonempty fully strict child-closed system" consequence is a direct
  contradiction with complete strict child closure, as in the repository's
  cut-pair reduction, and uses no measure-theoretic import.

## Hypotheses that do not transfer

- Arnoux–Ito's measure-disjointness needs unimodularity and all-pairs strong
  coincidence; nothing measure-theoretic is claimed here.
- Barge–Diamond gives *one* coincident pair, not a depth bound and not all
  pairs; it is not used for the lower bounds.
- Sirvent–Solomyak's termination equivalence is about the whole BPA; a sharp
  pairwise depth is not a termination proof for arbitrary seeds and does not
  give first-productivity depth of every balanced root.
- The five-chamber lower bounds depend on exact word order, not incidence
  (all splittings at fixed `s=a+b` share the incidence matrix).

## Negative controls / boundaries

- Same-incidence word-order countercontrol (the Python oracle): depths vary
  across splits of one incidence matrix, so no incidence-only depth formula.
- The prefix-satellite criterion is conditional: it does not supply the
  literal relation `tau(k)=tau(i)W` nor a `{i,j}` witness for arbitrary
  substitutions.
- Earlier equal-Parikh cuts with different next letters (e.g. `a>=2,b=0`
  level three, cuts `K+2` and `P`) are retained as explicit negative cases.

## Decision

**Proceed, narrowed.** The strong-coincidence notion, the BPA framework and
the one-pair existence result are standard and cited. Novelty is restricted to
the specialization: the exact sharp depth `D(a,b)` with pairwise minima
`(D,1,D)` for this family, and the prefix-satellite sufficient criterion as a
same-level variant of Lemma T. No general C4, G1, BH, A1′, PDS or PSC status
change.
