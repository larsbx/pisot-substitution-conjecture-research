# Rauzy-contact salvage from the stale cohomological-obstruction thread — 2026-10-23

**Status:** research-only salvage note. **Not a proof source, not a ledger promotion, and not a reopening or closure of any governed PSC claim.**

This note records what remains useful from an older exploratory thread after comparison with the current repository architecture. The authoritative theorem/status surfaces remain `claim_governance.toml`, `tools/make_ledger.py`, the generated proof bank/ledger, the live roadmap, and the source-linked proof notes.

In particular, do **not** infer theorem status from the GitHub open/closed state of an issue. At this writing the governed claim `UniversalBoundaryHitting` remains the authority for the universal statement.

## 1. What the stale thread explored

The older thread combined four ideas:

1. a proposed cohomological obstruction quotient (C_\sigma), with finite examples such as a \(\mathbb Z/7\mathbb Z\) action;
2. a Rauzy-fractal contact comparison between standard Tribonacci and the exploratory substitution
   [
   1\mapsto 2,\qquad 2\mapsto 3,\qquad 3\mapsto 132;
   ]
3. a finite nearest-class contact dynamics with two nonzero six-cycles and a class-zero cycle;
4. drift-corrected PSD / forcing diagnostics intended to distinguish algebraically persistent obstruction from geometrically inert ambiguity.

Those objects were useful exploratory scaffolding, but they are not part of the present proof architecture.

## 2. Salvage decisions

| Item from the stale thread | Current disposition |
| --- | --- |
| (C_\sigma) as a general PSC proof-regime classifier | **Do not promote.** It is not a load-bearing repository object and is not a replacement for the current exact overlap/boundary-hitting architecture. |
| "PDS can coexist with nonterminating canonical BPA" | **Reject.** Current repository results prove the relevant PDS-to-finiteness/seedwise-termination implications at their recorded scope; a different exploratory strand process must not be identified with the canonical balanced-pair closure without proof. |
| Formal arithmetic labels versus realized geometry | **Keep.** This matches the repository realization firewall: formal recurrence, exact overlap recurrence, contact geometry, and realized tiling/fibre statements are distinct layers. |
| Strong Rauzy/contact comparison as a finite diagnostic | **Keep as research-only control.** It can be compared against exact periodic-pair or box-automaton data, but it does not certify a universal theorem. |
| Exact six-step drift observed as (pm\pi_s(-1,0,3)) on the exploratory Tribonacci-family contact cycles | **Keep as a reproducibility target.** Re-derive it, if possible, from exact occurrence-labelled periodic-pair arithmetic rather than nearest-neighbour contact matching. |
| Drift-corrected forcing ratio below an empirical threshold | **Keep only as a diagnostic.** It becomes theorem-relevant only after an exact implication to offset-zero hitting / common-vertex forcing is proved. |
| Hodge/PSD/projective obstruction-complex superstructure | **Shelve.** Do not add another necessary-condition layer unless it supplies a completeness or hit-forcing theorem. |
| Purely Euclidean stable-plane argument as a general non-unit proof | **Reject.** Any general non-unit argument must retain the full representation-space hypotheses required by the repository firewall. |

## 3. The useful exact experiment

The only high-value downstream experiment from this thread is to test whether the observed contact-cycle drift survives replacement of the surrogate contact dynamics by exact occurrence-labelled periodic-pair data.

Use the repository's canonical exact objects:

- `kernel/psc/periodic_pair.mojo` for occurrence-labelled periodic-pair certificates;
- `kernel/psc/vertex_coincidence.mojo` / the box-automaton interface for the exact common-vertex verdict;
- the exact affine cycle identity
  [
  (M^r-I)w_0=\pi(P)-\pi(Q)
  ]
  supplied by the periodic occurrence data.

For an exploratory unit control such as the Tribonacci-family specimen above:

1. enumerate exact periodic-pair cycles that correspond to the contact states being compared;
2. derive the lifted displacement defect directly from the occurrence words (P,Q) and the exact cycle equation;
3. project only after the exact integer/algebraic identity is established;
4. compare the resulting projected defect with the previously observed
   [
   pm\pi_s(-1,0,3);
   ]
5. replay the exact PPVC / offset-zero verdict independently of any metric threshold.

There are then only two useful outcomes.

- **The drift survives exact occurrence arithmetic.** Preserve it as a concrete structural invariant/control and investigate whether it has a direct boundary-hitting interpretation.
- **The drift disappears.** Archive it as an artefact of the nearest-class contact surrogate. Do not repair the surrogate to recover the desired answer.

## 4. What would make the forcing functional mathematical

The empirical quantity
[
\Sigma_{\mathrm{corr}}(x)
=
\max_j\left|\sum_e x_e\langle r(e),\nu_j\rangle\right|
]
and its threshold comparison are not presently proof-bearing.

A theorem-grade use would require an implication of the form
[
\Sigma_{\mathrm{corr}}(x)<\tau_{\mathrm{corr}}
\quad\Longrightarrow\quad
\text{the exact periodic pair has an offset-zero descendant/common vertex}.
]

The threshold, directions, and residual must then be defined from exact repository objects, not from a calibrated point-cloud cutoff. Without such an implication the functional remains a visualization / prioritization diagnostic.

## 5. Current downstream relation

The current repository has moved to exact symbolic-line, carrier, descent, and boundary-hitting certificates on large scoped determinant-two families. Those results supersede the stale thread as the source of theorem progress.

The Rauzy/contact material therefore has only two legitimate roles downstream:

- **control geometry** for exact periodic-pair or boundary-hitting certificates;
- **hypothesis generation** for a future exact hit-forcing lemma.

It must not change the status of `UniversalBoundaryHitting`, `UniversalAlignedCoincidence`, G1, or PSC.

## 6. Practical stop rule

Do not build a new generalized obstruction complex from this thread.

Proceed only if an exact periodic-pair replay recovers a nontrivial lattice-drift identity or an empirical separation quantity can be upgraded to an exact common-vertex implication. Otherwise archive the exploratory computation and keep the present carrier/descent program as the theorem lane.
