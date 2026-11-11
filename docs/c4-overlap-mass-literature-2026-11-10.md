# C4 ordered overlap mass: literature stop/go

Date: 2026-11-10. Recorded before the new proof and control implementation.
Base: `main@b0a64e50bd9790c0033d7ff674c8b3a9e72b0a92` (PR #535).

## Proposed claim and decision

**Proceed with exact finite interval subdivision and occurrence counting.**
For the repository's top-minus-bottom packet `p = (a,b,r)`, put

\[
h(p)=\max\bigl(0,\min(\ell_a,\ell_b-\ell r)
                      -\max(0,-\ell r)\bigr).
\]

Under nonnegative letter lengths, a nonnegative scale `beta`, and the exact
equations `physicalLength ell (sigma a) = beta * ell a`, prove that

\[
\sum_{i<|\sigma(a)|}\sum_{j<|\sigma(b)|}
 h\bigl(a_i,b_j,Mr+\pi(\sigma(a)_{<i})-\pi(\sigma(b)_{<j})\bigr)
 =\beta h(p).
\]

The indices are actual ordered digit occurrences. Equal resulting packet
labels retain their separate summands. Zero lengths and zero scale may be
admitted by the elementary partition theorem; the positive-length,
positive-scale specialization matches the existing interior-successor
interface. No carrier, word legality, primitivity, irreducibility, Pisot
condition or compact attractor is needed for this identity.

Then derive finite row sums from literal occurrence fibers, identify the
deficit of a retained subfamily with the sum of explicitly omitted masses,
and derive the weighted forward/inverse count correspondence by finite
double counting. Reuse the existing `PhysicalMass.weighted_transpose` and
`weighted_deficit` theorems instead of proving their algebra again.

## Primary sources inspected

| Source and exact locator | Relevant construction | Transfer boundary |
|---|---|---|
| Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898v1](https://arxiv.org/html/1003.2898v1), section 4, equations (4.1), (4.2), (4.4), Theorem 4.1 | Inflated overlaps decompose over pairs of actual digits; the overlap graph retains edge multiplicity. | The interval specialization needs only ordered partitions. The source's spectral/productivity conclusion assumes an actual self-affine tiling with the Meyer property; those hypotheses are not supplied by formal packet labels. |
| Martensen, *A Generalized Balanced Pair Algorithm*, [arXiv:math/0309194v1](https://arxiv.org/html/math/0309194v1), section 2 and Theorem 3.10 | The positive Perron length row makes the geometric substitution self-similar; balanced-pair productivity is a separate hypothesis in the spectral implication. | An arbitrary positive row does not supply the exact scaling equation. The local mass identity neither proves termination nor constructs a coincidence. |
| Barge--Diamond, *Coincidence for substitutions of Pisot type*, [Bull. Soc. Math. France 130 (2002), 619--626](https://www.numdam.org/item/10.24033/bsmf.2433.pdf), pages 621--624, strand inflation and configurations | Ordered prefix displacements define actual inflated strand segments and their endpoint geometry. | The paper's Pisot configuration arguments concern genuine strands and use further geometry. They do not turn the finite mass identity into the uniform strict-carrier exclusion required by C4. |

The subdivision principle and finite double counting are standard. The
contribution sought here is a kernel-checked specialization to the existing
`OccurrenceTransport` packet convention, actual `markAt` addresses, and the
repository's weighted matrix consumer. No new general overlap theorem is
claimed.

## Existing repository results reused

- `OccurrenceSuccessor.offset_affine` derives the physical displacement of
  every actual digit pair from exact image-length scaling.
- `OccurrenceFinite.markEquiv` identifies literal word marks with their
  position indices. The new sum must use positions, not packet set support.
- `OccurrenceStrict` closes positive interior children in the represented
  packet support of an actual strict system.
- `PhysicalMass` already proves the generic weighted transpose and deficit
  identities. [The physical-mass refinement note](physical-mass-refinement-2026-11-08.md),
  sections 2--3, records the missing literal count and geometric adapters.
- [The finite-carrier controls](c4-finite-carrier-dual-controls-2026-11-10.md)
  and the latest [side ledger](side-notes-ledger.md) supply known wrong-row,
  repeated-occurrence and conservative-carrier controls.

## Finite counting interface

For ordered states mapping to quotient labels, let `m_i` be the cardinality
of label `i`'s fiber. A literal edge inventory, with explicit uniform
forward and incoming counts on each fiber, should imply

\[
m_iT_{ij}=m_jF_{ji}.
\]

With `H_i=m_i h_i` and
`delta_j = beta*h_j - sum_i F[j,i]*h_i`, the already proved consumer gives

\[
\beta H_j-(T^{\mathsf T}H)_j=m_j\delta_j.
\]

Uniformity is an explicit occurrence-count hypothesis, not a consequence
of merely naming a quotient. A size-two track-swap simplification needs a
proof that every orbit in the application is free. Mixed fixed/free
orbits require their actual weights. A literal omitted positive occurrence
gives a positive arithmetic deficit for the selected subfamily; it does
not by itself justify omitting that occurrence from the geometric problem.

## Required controls and non-claims

1. Repeated equal packet labels must contribute more than once. Compare
   the full ordered sum with its deliberately deduplicated version.
2. Boundary touching contributes zero mass and must not be treated as an
   interior occurrence or as a positive loss.
3. The known `sigma = 1/012/1` fixture with the wrong positive row `(2,1,1)`
   must reject the scaling premise. Its correct row `(1,2,1)`, scale two,
   supplies a conservative strict non-PIP control.
4. Deleting a genuine positive child must produce exactly its omitted mass;
   deleting only a zero-mass boundary child must produce zero deficit.
5. A finite mixed-orbit count example must satisfy the weighted identity
   and reject the unweighted transpose shortcut. A reversed matrix-index
   mutation must be detected separately.
6. Empty words, nonnegative degenerate lengths and an empty occurrence
   family are partition boundary cases, not evidence for interior seriality.

On the complete represented interior support of a strict carrier, every
positive child is retained. The expected mass equation is consequently
conservative: `F h = beta h`. The present work must preserve that fact.
It cannot manufacture the positive loss needed by the existing mass
exclusion theorem. Actual compact overlap sets, nonunit Haar scaling,
coverage of the relevant geometry, and a justified losing source remain
separate obligations. C4, Concentration, global G1 and PSC remain open.

## Verification plan

Compile the new Lean modules and run the isolated whole-bank axiom audit
using the pinned toolchain. Add small exact canonical Mojo controls and
bounded Quint adversarial controls if the executable contract is extended;
retain actual occurrence indices and exact arithmetic. Bind acceptance to
the published revision, record generated-bank and provenance checks, and
append the resulting side findings in the same commit. No broad census or
new numerical cutoff is needed.
