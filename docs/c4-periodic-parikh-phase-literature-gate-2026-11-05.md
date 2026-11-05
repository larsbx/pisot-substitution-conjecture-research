# Periodic-phase Parikh rigidity: literature stop/go gate

**Decision (2026-11-05): proceed with a narrowed target.** Keep the
phase-wise rank/size theorem and the exact phase-balance identity of
[the periodic phase note](c4-periodic-parikh-phase-rigidity-2026-11-04.md)
as a *specialization* of standard Perron--Frobenius cyclic structure and of
the invariant-subspace consequence of an irreducible characteristic
polynomial. No novelty is claimed for either ingredient. Do not run the
proposed equality-case template enumeration for the 36 sources with
incidence `M_2`: merged #491 already excludes every strict component there.

This gate was written *after* the PR #484 implementation, at review time.
It is recorded so that the scope decision is visible; it does not
retroactively turn that ordering into the AGENTS.md "review first" order.

## Proposed claim and experiment

For a supplied occurrence-complete, fully strict, strongly connected set `C`
of actual noncoincident balanced pairs of a primitive irreducible ternary
Pisot substitution with incidence `M`, with Parikh matrix `P` and literal
child matrix `N` satisfying `P N = M P`: if `N` has period `h`, every cyclic
class `C_k` has `rank P_k = 3`, `chi_(M^h)` divides `chi_(B_k)` for the
diagonal block `B_k` of `N^h`, `|C_k| >= 3`, hence `|C| >= 3h`; and the
class-restricted right Perron vectors carry equal Parikh mass `P v / h`.
The executable part is a bounded exact audit of a supplied integer packet
`(M, P, N, phases, h)`; it constructs no word-derived SCC.

## Primary sources and terminology

| Source and location | Relevant result | Transfer boundary |
| --- | --- | --- |
| E. Seneta, *Non-negative Matrices and Markov Chains*, 2nd ed., Springer Series in Statistics, Springer, 1981; Chapter 1 (irreducible matrices, periodicity, Perron--Frobenius theory) | An irreducible nonnegative matrix of period `h` permutes `h` cyclic classes; `N^h` is block diagonal on them, each block primitive with Perron root `beta^h`; the Perron vector is unique up to scale. | Transfers verbatim to `N`: irreducibility of `N` is a *hypothesis* (strong connectivity of the supplied `C`), not something the audit certifies. |
| R. A. Horn and C. R. Johnson, *Matrix Analysis*, 2nd ed., Cambridge University Press, 2013; Chapter 8 (positive and nonnegative matrices) | Same cyclic (imprimitive) normal form and Perron--Frobenius statements, in the terminology "irreducible", "primitive", "index of imprimitivity". | The field's term for `h` is the *index of imprimitivity* (graph period). Our "phase" = cyclic class. |
| D. Lind and B. Marcus, *An Introduction to Symbolic Dynamics and Coding*, Cambridge University Press, 1995; Chapter 4 (Perron--Frobenius theory, irreducible components, cyclic structure) | Period of an irreducible graph and its period classes, in the symbolic-dynamics language used for substitution/balanced-pair graphs. | Applies to the occurrence graph of `N`, not to the substitution's own incidence `M` (which is primitive). |
| D. S. Dummit and R. M. Foote, *Abstract Algebra*, 3rd ed., Wiley, 2004; Section 12.2 (rational canonical form) | A linear map on `Q^n` whose characteristic polynomial is irreducible over `Q` has only the trivial invariant subspaces `0` and `Q^n`, and any invariant quotient's characteristic polynomial divides a block's. | This is the whole engine of the rank statement: applied to `M^h` on the rational image of `P_k`. Needs `chi_(M^h)` irreducible, supplied by the next row. |
| M.-J. Bertin, A. Decomps-Guilloux, M. Grandet-Hugot, M. Pathiaux-Delefosse and J.-P. Schreiber, *Pisot and Salem Numbers*, Birkhäuser, 1992 | Basic facts on Pisot numbers: all Galois conjugates lie strictly inside the unit disc; powers of a Pisot number are Pisot numbers. | Our Lemma 1 (`beta^h` still has degree three, so `chi_(M^h)` is irreducible) is an elementary consequence for the *prime-degree* cubic case; it is re-proved in the note and checked in the oracle by exact integer roots. |
| V. F. Sirvent and B. Solomyak, "Pure discrete spectrum for one-dimensional substitution systems of Pisot type", *Canad. Math. Bull.* 45 (2002), 697--710 | Balanced-pair algorithm and its relation to coincidence/pure discrete spectrum for Pisot substitutions. | Supplies the balanced-pair vocabulary only. Their termination results are not imported: the existence or non-existence of a strict SCC is exactly what remains open. |

The matrix-theory statements are standard textbook material cited at
chapter granularity; they were not re-read page by page in this session,
and no theorem number is asserted for them. Nothing in the note depends on
a statement beyond those classical facts.

## Hypotheses that transfer and those that do not

- **Transfer:** cyclic classes and block-diagonality of `N^h` (any
  irreducible nonnegative integer `N`); trivial rational invariant
  subspaces of `M^h` (any irreducible cubic Pisot `M`, any `h >= 1`);
  uniqueness of the positive Perron vector of `M`, used for equal phase
  masses.
- **Do not transfer:** realizability. A packet satisfying every algebraic
  conclusion need not come from actual balanced words; the synthetic
  `P = [I, M, ..., M^(h-1)]` saturations are explicitly not word systems.
  Reducible `M`: the rank argument fails, and the real strict four-state
  system of `10/102/211` (reducible cubic, rank two) is the control.

## Known negative controls and counterexamples

- Real strict, primitive but reducible-characteristic four-state system
  (`10/102/211`, #462): satisfies `P N = M P`, refused by the rank check.
- Broken intertwiner and mislabelled phase: refused by the intertwiner and
  phase-edge checks respectively.
- `h = 3` on a six-state packet: refused by the input budget `r >= 3h`
  only, which is a shape refusal and is labelled as such in the tests.
- Merged #491 (direct source certificates): for all 36 sources with
  `M_2`, no nonempty strict component exists at all, so `M_2` packets can
  only ever be algebraic controls.

## Decision

**Proceed, narrowed.** Novelty is restricted to the specialization to
supplied strict balanced-pair SCCs (the *per-phase* rank three, the bound
`|C| >= 3h`, and the Perron-weighted per-phase Parikh equipartition) and
to its bounded exact audit with named controls. **Stop** the equality-case
template search for `M_2` sources (superseded by #491). **Do not infer**
existence or exclusion of a strict SCC, or any C4, G1, BH, A1', PDS or
PSC status change.
