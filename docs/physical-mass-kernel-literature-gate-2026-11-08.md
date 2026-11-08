# Source-SCC mass-loss kernel: literature decision

Date: 2026-11-08. Decision: **proceed with a narrowed formalization**.
This gate precedes the new Lean and Quint code. It continues the inspected
[PR #515 argument](https://github.com/larsbx/pisot-substitution-conjecture-research/blob/51dd090a6aefeb92210410a3f7e20d51926d7e86/docs/c4-physical-overlap-mass-2026-11-07.md),
not a claim of new Perron--Frobenius theory.

## Exact target

For an arbitrary finite real matrix `T >= 0`, a strictly positive vector `h`,
and a nonnegative vector `v`, prove that `Tv >= theta v` and
`transpose(T) h <= theta h` imply saturation and zero on every coordinate
reachable from a positive deficit. Prove, rather than assume, that every
finite directed graph vertex has a source strongly connected component
ancestor. A positive deficit in each source component then forces `v = 0`.
Edges have the explicit orientation `i -> j` iff `T[i,j] > 0`.

## Primary sources inspected

1. Bit-Shun Tam and Hans Schneider, *On the core of a cone-preserving map*,
   Transactions of the AMS 343 (1994), 479--524,
   [§2, Theorem 2.1 and preceding definitions](https://people.math.wisc.edu/hans/paper_archive/scanned_papers/hs106.pdf).
   Their graph uses row-to-column nonzero entries, and the Frobenius--Victory
   theorem describes nonnegative eigenvectors by accessible distinguished
   classes. The present kernel is an elementary positive-dual-vector
   specialization, using finite sums and reachability rather than importing
   their spectral theorem. Conservativity is a real boundary: an isolated
   conservative block can retain a nonzero vector.
2. Shigeki Akiyama and Jeong-Yup Lee, *Algorithm for determining pure
   pointedness of self-affine tilings*,
   [§4, (4.2) and Theorem 4.1](https://arxiv.org/pdf/1003.2898).
   Occurrence multiplicities are part of the overlap graph. The spectral
   tiling criterion assumes an actual self-affine tiling and the Meyer
   property. Those geometric hypotheses do not follow from a finite matrix
   certificate. Neither deleting occurrences nor identifying potential
   overlaps with actual overlaps is licensed by this formalization.
3. Milton Minervino and Jörg M. Thuswaldner, *The geometry of non-unit
   Pisot substitutions*,
   [Lemmas 3.1 and 3.3](https://arxiv.org/pdf/1402.2002).
   The non-unit representation space has Haar scaling by the reciprocal
   Pisot root; Perron lengths are rationally independent in the stated
   irreducible setting. These support the written source construction but
   do not provide the source-to-matrix refinement, a loss in every component,
   or a one-step synchronizing newborn cut.

## Hypotheses that transfer

Finite nonnegative matrices, exact repeated occurrences, positive physical
mass, and a separately justified overlap supersolution transfer as explicit
inputs. The abstract implication has no alphabet size, Pisot, irreducibility,
primitivity, or uniform state-cap premise. It is uniform over supplied finite
graphs; it does not prove that the required finite graph exists for every
substitution.

The physical subdivision orientation is opposite the inverse graph. For
constant track-swap orbit size, its multiplicity matrix is `transpose(T)`;
mixed orbit sizes require the weighted identity `m_i T_ij = m_j F_ji` and
the mass `H_i = m_i h_i`. These are refinement obligations, not conventions
to be silently exchanged.

## Negative controls and decision

Preserve conservative source components, losing sinks, deleted repeated
occurrences, a wrong transpose, zero mass, and incomplete root coverage.
Some controls invalidate the algebraic premise; others leave a sound
algebraic theorem about the wrong supplied object. The latter must be
rejected by source binding, not described as a refutation of the theorem.

Proceed with the reusable conditional kernel, an independent bounded Quint
model, and exact-revision source replay. The next uniform research premise
is exclusion of conservative inverse source components on a complete,
realized strict-PIP carrier, together with the independent reduction to the
actual one-step `Sync_+`/`Sync_-` newborn demanded by issue #461. General C4,
PSC, and that geometric reduction remain open.
