# Phase-lattice index conservation: literature stop/go gate

**Decision (2026-11-05): proceed with a narrowed target.** Keep Theorem 1,
Corollary 2 and Proposition 3 of
[the phase-lattice note](c4-phase-lattice-index-conservation-2026-11-04.md)
as a *specialization* of standard integer-lattice facts (index of a
sublattice as a ratio of determinants, multiplicativity of the index along a
chain, Smith normal form, localization at primes not dividing the
determinant) to the cyclic classes of a supplied strict balanced-pair SCC.
No novelty is claimed for any of these ingredients.

This gate was written *after* the PR #486 implementation, at review time.
It is recorded so that the scope decision is visible; it does not
retroactively turn that ordering into the AGENTS.md "review first" order.

## Proposed claim and experiment

For a supplied occurrence-complete, fully strict, strongly connected set `C`
of actual noncoincident balanced pairs of a primitive irreducible ternary
Pisot substitution with incidence `M`, `m = det M != 0`, Parikh matrix `P`
and literal child matrix `N` with `P N = M P`, graph period `h` and cyclic
classes `C_k` with `rank_Q P_k = 3` (PR #484): the phase lattices
`L_k = P_k Z^|C_k|` satisfy `M L_k ⊆ L_(k+1)` with integer index
`t_k = |m| g_k / g_(k+1)`, `prod t_k = |m|^h`, prime support of each `t_k`
inside that of `m`, constant `p`-primary Smith factors for `p ∤ m`, exact
lattice equality when `|m| = 1`, and nonsingular one-step blocks with
`|det A_k| = t_k` when `|C| = 3h`. The executable part is a bounded exact
audit of a supplied integer packet `(M, P, N, phases, h)`; it constructs no
word-derived SCC.

## Primary sources and terminology

| Source and location | Relevant result | Transfer boundary |
| --- | --- | --- |
| M. Newman, *Integral Matrices*, Pure and Applied Mathematics 45, Academic Press, New York, 1972; Chapter II (equivalence and the Smith normal form) | Smith normal form of an integer matrix; the product of the first `k` invariant factors is the gcd of the `k x k` minors, so the index of the column lattice of a full-rank `3 x r` integer matrix is the gcd of its `3 x 3` minors. | Transfers verbatim to `g_k = [Z^3 : L_k]`; the audit computes exactly this gcd. |
| H. Cohen, *A Course in Computational Algebraic Number Theory*, Graduate Texts in Mathematics 138, Springer, 1993; §2.4 (Z-modules and the Hermite and Smith normal forms) | Algorithms and basic theory for sub-Z-modules of `Z^n`: index via determinants, Hermite/Smith normal forms, elementary divisors. | Supplies the computational definition of the lattice index; the bounded audit uses minor gcds rather than an HNF/SNF routine, which is equivalent for the index. |
| J. W. S. Cassels, *An Introduction to the Geometry of Numbers*, Grundlehren der mathematischen Wissenschaften 99, Springer, 1959; Chapter I (lattices and sublattices) | For full-rank lattices `A ⊆ B`, `[B : A] = d(A)/d(B)`; hence `[B:A] = [Z^3:A]/[Z^3:B]` and indices multiply along chains `A ⊆ B ⊆ C`. | This is the whole engine of Theorem 1: `[Z^3 : M L_k] = |m| g_k` and the chain `M L_k ⊆ L_(k+1) ⊆ Z^3`. |
| M. F. Atiyah and I. G. Macdonald, *Introduction to Commutative Algebra*, Addison-Wesley, 1969; Chapter 3 (rings and modules of fractions) | Localization is exact; a finite abelian group whose order is prime to `p` vanishes after tensoring with `Z_(p)`. | Gives `L_(k+1) ⊗ Z_(p) = M (L_k ⊗ Z_(p))` for `p ∤ m`, hence constant `p`-primary Smith factors. Says nothing at primes dividing `m`; that is Corollary 2's budget. |
| E. Seneta, *Non-negative Matrices and Markov Chains*, 2nd ed., Springer Series in Statistics, Springer, 1981; Chapter 1 | Cyclic classes of an irreducible nonnegative matrix of period `h`; every edge goes from class `k` to class `k+1`. | As in the [#484 gate](c4-periodic-parikh-phase-literature-gate-2026-11-05.md): irreducibility of `N` is a hypothesis (strong connectivity of the supplied `C`), not certified by the audit. |
| M. Minervino and J. M. Thuswaldner, "The geometry of non-unit Pisot substitutions", *Ann. Inst. Fourier* 64 (2014), 1373--1417 ([arXiv:1402.2002](https://arxiv.org/abs/1402.2002)) | In the non-unit case the representation space carries finite places dividing the Pisot number; residues modulo `M^q Z^3` record that information. | Motivates reading Corollary 2's `p | det M` transport alongside the `Z^3 / M^q Z^3` residue tables of [#493's successor note](c4-nonunit-residue-occupancy-2026-11-04.md) and the [M-adic counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md). No theorem of theirs is imported into Theorem 1. |

The lattice and localization statements are standard textbook material cited
at chapter or section granularity; they were not re-read page by page in this
session, and no theorem number is asserted for them. Nothing in the note
depends on a statement beyond those classical facts.

## Hypotheses that transfer and those that do not

- **Transfer:** index identities for any full-rank sublattices of `Z^3`;
  `[Z^3 : M L] = |det M| [Z^3 : L]` for any nonsingular integer `M`;
  localization at `p ∤ m`; cyclic class structure of any irreducible
  nonnegative `N`.
- **Needs PR #484:** full rank of each `P_k`. Without it `L_k` is not of
  finite index and `g_k` is undefined (the audit refuses with a rank error).
- **Needs `m != 0`:** with `det M = 0` the identity `[Z^3 : M L] = |m| [Z^3:L]`
  is meaningless; the audit refuses singular `M`. The unimodular case
  `|m| = 1` is a corollary, not a separate hypothesis.
- **Do not transfer:** realizability. A packet satisfying every lattice
  conclusion need not come from actual balanced words; the synthetic
  `M_2` and Tribonacci packets of the note are explicitly not word systems.

## Known negative controls and counterexamples

- Real strict, primitive but reducible-characteristic four-state system
  (`10/102/211`, #462): satisfies `P N = M P`, refused by the rank check.
- Broken intertwiner, mislabelled phase, missing child column and singular
  `M`: refused by the corresponding input checks.
- The product, prime-support and unimodular checks of the audit are
  algebraic identities of the computed `t_k`; they are internal invariant
  asserts and are **not** counted as negative controls. No public entry
  point accepts a caller-supplied `t_k` allocation.
- Merged #491 (direct source certificates): for all 36 sources with `M_2`,
  no nonempty strict component exists, so `M_2` packets are only algebraic
  controls.

## Decision

**Proceed, narrowed.** Novelty is restricted to the specialization to
supplied strict balanced-pair SCCs (the phase lattice flow, the
determinant-prime budget `prod t_k = |m|^h` with its period-two allocation
list, unit-case lattice equality, and the equality-size block determinant
condition) and to its bounded exact audit with named controls. **Do not
infer** existence or exclusion of a strict SCC, or any C4, G1, BH, A1', PDS
or PSC status change.
