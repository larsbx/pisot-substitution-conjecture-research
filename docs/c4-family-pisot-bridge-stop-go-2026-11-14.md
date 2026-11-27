# Family arithmetic and full-factor bridge: pre-code decision

Date: November 14, 2026. Base source:
`32015cfb9d0914cedc9867f3290ea4bcdbbbb3b7` (PR #572).

**Proceed with two precise formal obligations:** prove the literal family's
primitive irreducible Pisot arithmetic, and prove the single-seed correspondence
between the existing termination predicate and the full-iterate factor condition.
This note precedes the new proof implementation. It reuses the
[six-source family screen](c4-parameter-family-stop-go-2026-11-14.md) and records
a fresh inspection of the three primary sources below. Neither standard
polynomial arguments nor the published spectral implication are claimed as new.

## Exact targets

Use the existing literal substitution
`sigma_k(0)=1`, `sigma_k(1)=0 1^k 2`, `sigma_k(2)=001`.
For natural `k >= 1`, bind actual image-letter counts to

\[
M_k=\begin{pmatrix}0&1&2\\1&k&1\\0&1&0\end{pmatrix},\qquad
M_k^2=\begin{pmatrix}1&k+2&1\\k&k^2+2&k+2\\1&k&1\end{pmatrix}>0.
\]

Prove the characteristic polynomial of the rational cast of that same incidence
matrix is `X^3-k X^2-2 X-2`, is irreducible over the rationals, and has a real
root `beta>2` with every different complex root of modulus less than one.
No independently supplied matrix or root hypothesis may replace these targets.

For a finite alphabet and an actual irreducible balanced seed, relate
`Psc.StrictSystem.TerminatesWithCoincidence` to the finite set of all factors
in all actual iterated reductions, each of which eventually produces a singleton
diagonal factor. Preserve the literal seed and the existential path quantifier.
The intended family specialization uses the accepted `01/10` theorem for `k>=2`.

## Primary sources and hypothesis checks

1. Barge, Stimac and Williams, *Pure discrete spectrum in substitution tiling
   spaces*, [author PDF](https://web.math.pmf.unizg.hr/~sonja/PDSfinal.pdf),
   section 3 and Corollary 2. The combinatorial condition concerns all factors
   in full iterates. One unequal-letter swap seed suffices under irreducible
   Pisot and the paper's standing primitive, aperiodic and finite-local-complexity
   assumptions. No unimodularity premise is inserted into this criterion.
2. Minervino and Thuswaldner, *The geometry of non-unit Pisot substitutions*,
   [publisher PDF](https://www.numdam.org/item/10.5802/aif.2884.pdf), section 8.2
   and Theorem 9.10. Strong coincidence and geometric property (F) play separate
   roles. The family's determinant is two; a unit-only or strong-coincidence-only
   shortcut cannot replace the full hypotheses of the selected route.
3. Akiyama, Gahler and Lee, *Determining pure discrete spectrum for some
   self-affine tilings*,
   [publisher PDF](https://dmtcs.episciences.org/en/articles/2089/download),
   Proposition 2.2. The cubic trace-at-most-two result already covers the first
   two parameters mathematically. Here the trace is `k`, so this source does not
   supply the unbounded higher-parameter conclusion or the literal Lean proof.

## Reconstruction and controls

The rational-root proof reduces a monic integer cubic root to integer divisors
of two and excludes all candidates for `k>=1`. An intermediate-value bracket
between `2` and `k+2` gives the real root. Factoring out that root leaves a
quadratic with product `p=2/beta` in `(0,1)`; an exact real/imaginary calculation
can prove the other roots have squared norm `p`. Existing repository proofs
provide these standard proof patterns without requiring new numerical machinery.

For the factor adapter, a full child path ending at a noncoincident state is a
`ChildNC` path. A coincident irreducible factor is a singleton diagonal. Thus
the all-factor set is contained in the finite noncoincident-parent reachable
set union the finite set of singleton diagonals. The existing path/iterate
equivalence supplies the eventual-coincidence correspondence.

Controls retain the false stronger variants: `k=0` cannot inherit the Pisot
claim; one-step exits fail at `k=2`; a selected avoiding cycle need not be a
nonproductive closed component; and finiteness alone supplies no coincidence.
The adapter must not replace one seed by a union over all swap seeds, or drop
the irreducibility/finite-alphabet premises needed by its proof.

## Scope of the decision

Arithmetic and full-factor correspondence are suitable for new axiom-free Lean
proofs. The tiling realization, aperiodicity justification and the published
spectral implication require their own explicit mathematical account; the
spectral theorem is not installed as a Lean axiom. A family application does not
discharge universal BH, residual A1-prime, C4 or PSC. A separate parallel review
must address those universal obligations directly. Pending human review does not
block continued research under the repository's progression convention.
