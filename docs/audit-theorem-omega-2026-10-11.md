# Theorem Ω sufficiency review and PR #235 reconciliation — 2026-10-11

## Decision and source identities

Reconcile PR #235 head `7e13a28ec0962a2e09c7666d83ab360962f07b8f`
with main `66df3e4`. This is an independent assistant examination of the
mathematical argument and primary sources, not independent human acceptance.
No failed mathematical step was identified in the sufficiency route. The
human-review acceptance condition stated by the original audit remains open;
there is no authorization to record an automated examination as that acceptance.
The universal PSC and FormalProductivity obligations remain open.

The two merge conflicts concern the README's finite-domain summary and the
append-only side-notes ledger. Preserve main's entire ledger as an exact prefix,
then append all four PR audit records and this session's record. Preserve the
October 8 and October 9 evidence packets byte-for-byte. The proof note merges
without a conflict and retains main's tiling-hull and proof-ledger clarifications.
The generated proof bank is regenerated from its generator; the current main
has 97 claim records, 27 named Lean proofs and 269 source openings. The claim
table, statuses, dependency models, Lean sources and open gates are unchanged
relative to main. Only the two existing PDS source line locators move.

## Mathematical examination

**Length basis and discreteness.** Normalize the positive left eigenvector
in `K = Q(beta)`. Its coordinates span a nonzero rational subspace `W` of `K`
stable under multiplication by beta, since `ell M = beta ell`. For a nonzero
coordinate `h`, the three elements `h, beta h, beta^2 h` are independent:
otherwise the irreducible cubic of beta would have degree at most two.
They lie in `W`, so `W = K` and the three coordinates are a rational basis.
The all-real embedding matrix, or the real embedding plus real/imaginary
coordinates of a complex pair, is invertible. Its image of `Z^3` is a full-rank
lattice. This lattice is in the full Minkowski space, not in the physical
one-dimensional line, where the length module need not be discrete.

The descendant recurrence is multiplication by beta plus a finite prefix
difference. Each contracting embedding stays bounded by the maximum of its
initial modulus and `C/(1-|beta_k|)`. Interior overlap bounds the physical
coordinate by `ell_max`. Compactness in the full Minkowski space therefore
gives finitely many descendant offsets. Solving the affine recurrence on a
cycle yields the same contracting bound; the trace-dual basis transfers it to
the integral coordinate radii. For a complex pair the trace contribution is
twice a real part and is bounded by twice the product of moduli. None of these
steps takes `M^{-1}` on the integral lattice or assumes determinant ±1.

**Signed realized-overlap inclusion.** For LMS's overlap `(T,y,S)`, with
left endpoints `u_i` and `u_j`, translate `y+T` to zero. The bottom tile then
starts at `t = u_j-u_i-y`. This is the negative of LMS's class displacement.
Every endpoint difference is a signed sum of lengths along a finite tile
interval; the same holds for the return translation `y`. Thus `t` is in the
formal length module and obeys `-ell_j < t < ell_i`. After substitution the
top and bottom endpoints differ by
`beta*t + prefix_bottom - prefix_top`. Equal types and zero displacement
are exactly geometric coincidences. This embeds every realized overlap class
and all its geometric descendants into the formal graph. It proves inclusion,
not equality, and supports only the positive sufficiency certificate.

**Power and fixed tiling.** Primitivity and growth provide a power with an
interior occurrence `sigma^p(a) = u a v`, both flanking words nonempty. Put
`Q = beta^p`, `x = length(u)/(Q-1)` and the parent tile at `-x`.
The length identity `length(u)+ell_a+length(v)=Q*ell_a` proves
`0 < x < ell_a`. The interior child starts at `-Q*x+length(u)=-x`.
Successive substituted patches are nested, legal and exhaust both directions.
Every legal patch occurs with bounded gaps by primitivity, so their limiting
fixed tiling is repetitive. Finitely many labelled interval types give FLC
here: on any bounded interval the number of tiles is bounded by the positive
minimum length. Primitivity also ensures that the language and translation
hull of the power agree with those of the original substitution.

A formal coincidence witness for a realized overlap is a geometric child
path. Once it reaches a coincidence, coincident subtiles provide continued
geometric paths of every larger depth. Pad to a multiple of `p` and group the
steps into power-substitution edges. Although the certificate implementation
stops expanding coincidences, this padding uses the unstopped geometric
subdivision, so it is not an assertion about nonexistent exported edges.
The finitely many realized classes supply a uniform witness bound; no uniform
bound on all formal starting offsets is asserted. Powers of a Pisot number
are still Pisot: every other conjugate is a power of a contracting conjugate.

## Imported hypotheses checked directly

The primary arXiv PDFs were inspected, including the definitions around the
following statements. The determinant of the incidence matrix is unrestricted.

| Source | Actual hypothesis and application |
| --- | --- |
| [Lee–Moody–Solomyak, arXiv:0910.4450](https://arxiv.org/pdf/0910.4450), Theorem 4.7, Definition 6.7, Lemmas 6.8–6.9 | Repetitive fixed point of a primitive tile substitution with expansive map and Meyer same-type return vectors. Lemma 6.8 makes the realized class graph finite; coincidence reachability supplies the density criterion of Theorem 4.7. The constructed power tiling meets the fixed-point hypothesis. The paper's later lattice-substitution section is not being imported. |
| [Akiyama–Lee, arXiv:1003.2898](https://arxiv.org/pdf/1003.2898), Definition 2.4, Theorems 2.5 and 2.7 | Self-affine tiling means the requisite repetitive primitive FLC fixed tiling. Theorem 2.7 requires diagonalizable expansion with algebraically conjugate eigenvalues of equal multiplicity. The one-dimensional map `[beta^p]` satisfies this and its singleton spectrum is a Pisot family, giving Meyer return vectors. Theorem 2.5 gives the overlap-coincidence/PDS equivalence. Their algorithmic potential overlaps are not identified with this repository's formal overlaps. |
| [Lee–Solomyak, arXiv:1002.0039](https://arxiv.org/pdf/1002.0039), Definitions 2.3 and 2.7, Corollary 2.13, Theorem 4.3 | The same expansion hypotheses give Meyer control points. Same-type returns lie in their difference set. To infer that returns themselves are Meyer one also needs relative denseness (repetitivity) and uniform discreteness of their difference set, which follows from the Meyer finite-difference property. The direct return-vector version in Akiyama–Lee avoids this intermediate translation. |
| [Clark–Sadun, arXiv:math/0201152](https://arxiv.org/pdf/math/0201152), Theorem 3.1 and Corollary 3.2 | Primitive aperiodic substitution subshift; exactly one incidence eigenvalue of modulus at least one, counted with multiplicity. PIP meets this. No invertibility over `Z` or unimodularity occurs in this conjugacy criterion. |

**Symbolic bridge.** PIP is aperiodic: a periodic primitive subshift would have
rational positive letter frequencies, hence a rational right Perron vector;
`M f = beta f` would force beta rational, contradicting its irreducible cubic.
Choose the constant roof in Clark–Sadun by matching the positive Perron
component of the two length vectors. Their difference lies in the contracting
left eigenspaces, so its product with `M^n` tends to zero (Theorem 3.1 with
`k=0`). Corollary 3.2 gives the conjugacy to a roof-`c` suspension. Unique
ergodicity ensures this conjugacy carries the invariant measures.
The suspension measure is `mu_shift × dt/c`; away from the null roof boundary,
its time-`c` map is `shift × identity`. A pure-point flow has a complete
eigenbasis for every time map, including this nonergodic map. Functions
depending only on the subshift coordinate form a reducing subspace, whose
restriction is the shift's Koopman operator, hence pure point. This also
explains why ergodicity of the time-`c` map is neither asserted nor needed.

The finite-domain dependency list in the proof note previously named only
LMS/LS for route (a), despite using Clark–Sadun above. Correct that list to
include the symbolic bridge explicitly. Add the fixed-tile endpoint inequality.
These are explanatory repairs; no proof-ledger record or status is promoted.

## Computational evidence and remaining acceptance conditions

The observed PR head has seven successful workflows. Research run
[37916615755](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/37916615755)
includes a completed 70-file Mojo suite, certificates and standing census, and
the Lean build/axiom audit (146 declarations, 92 theorems, all named proofs
reached). Box run
[37916615696](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/37916615696)
has all thirteen jobs successful. Independently retrieved actual output lines
give twelve slices totalling 135,990 productive specimens and 24,486 total-8
specimens, all with zero caps/failures/nonproductive outputs. Count each job
once: logs print both the program output and the later grep match.

The logs identify checkout `6c440aa0b02afd1cb8d1d8b49848a9ee35e30a15`.
Git tree comparison gives `e89b686321137090b2c0eeb752edb820cd0b2024`
for both that checkout and PR head `7e13a28`; they are exact-tree evidence for
the existing head, not a compiled receipt for the new reconciliation.
The independently rerun exact domain oracle again gives intersection 14,670
and union 145,806. Cardinality alone is not a graph-productivity proof.

New reconciliation checks and environment failures are preserved separately
in [the October 11 packet](../evidence/omega-audit-reconciliation-2026-10-11/README.md).
Local Mojo provisioning encounters an unavailable conda-forge package; local
Lean provisioning installs the pinned release but its executable cannot locate
the application in this runtime. Those failures receive no execution credit.
The historical five representative replays remain preserved; they are not
described as newly rerun exports. No failed overlap-kernel contract was found.

Acceptance still needs an attributable independent human mathematical review
of this sufficiency chain and passing required checks on the reconciled head.
The imported spectral theorems remain imports, and Ω is not Lean-formalized.
The necessity direction's Barge coincidence-rank imports are outside this
sufficiency examination. A failed formal certificate is not by itself a PDS
counterexample. No universal PSC conclusion follows from the finite census.
