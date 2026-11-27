# Three determinant bands: complete literal closure in Lean

## Result and exact scope

For every pair of natural parameters

\[
 r\ge12,\qquad r\le k\le r+2,
\]

Lean constructs a real root \(k<\beta<k+1\) of
\(X^3-kX^2-2X-r\), proves primitive irreducible Pisot arithmetic for the
**original** substitution

\[
 \sigma_{k,r}:\quad 0\mapsto1,\quad
 1\mapsto0\,1^k\,2,\quad 2\mapsto0^r\,1,
\]

and proves that **every strict integral typed packet** has a finite path
through actual original child occurrences to equal-letter integral zero.
The conclusion retains both occurrence ordinals at every edge. It covers
arbitrary initial letter labels and every integral displacement satisfying
strict overlap, with no finite search bound on the source.

The aggregate endpoint is
`Psc.BHThreeBandClosure.family_closure`. Its only inputs are the parameters
and the three inequalities displayed above. Its `FamilyClosure` conclusion
contains the actual incidence arithmetic, positive eigenlengths, the
ordered all-source exit, all-pairs left strong coincidence, and exclusion
of every finite strict balanced-pair system, all for one constructed root.
It assumes no root, classification, entry, rank, termination or coincidence
certificate.

This completes the Lean obligations left open by the
[diagonal residual derivation](bh-diagonal-residual-exit-2026-11-27.md) and
the [third-level window construction](bh-third-level-windows-2026-11-24.md).
The [spectral transfer note](bh-three-band-spectral-transfer-2026-11-27.md)
separates formal endpoints from the published dynamical implication and
from earlier parameter regions with different evidence scopes. No general
BH, residual A1′, general C4 or PSC assertion is discharged by a theorem
about this family. Independent human review remains pending.

## Completed proof obligations

| Obligation | Actual compiled endpoint | What is discharged |
| --- | --- | --- |
| Parameter existence | `BHDiagonalParameters.family_root_exists`, `near_diagonal_root_exists` | The expanding root is constructed from natural parameters |
| Outer diagonal descent | `BHDiagonalOuter.outer_step` | An admissible actual child lowers energy outside an explicit cutoff |
| Complete residual classification | `BHDiagonalClassificationFull.residual_classification` | Arithmetic bridge hypotheses are derived from the actual cubic family |
| Signed residual progress | `BHDiagonalProgress.residual_progress` | Both signs, all axes and all four resonant pairs have literal exit or decrease |
| Finite termination | `BHDiagonalTermination.central_hits_labelled_zero` | The progress alternative yields a finite actual labelled exit |
| Third-level entry | `BHThirdLevelEntry.run_family_entry_ordered` | Actual spacing, clean window, locator and reverse ancestry are constructed |
| All original strict sources | `BHDiagonalAllSources.three_band_all_source_exit` | Entry and central termination are composed across all three bands |
| Actual Pisot arithmetic | `BHDiagonalPisot.primitive_irreducible_pisot`, `BHNearDiagonalPisot.primitive_irreducible_pisot` | Primitivity, actual characteristic irreducibility and contracting conjugates |
| Arithmetic on the larger domain | `BHHigherDeterminantPisot.primitive_irreducible_pisot` | Actual primitive irreducible Pisot arithmetic and positive literal eigenlengths for every `4<=r<=k` |
| Literal strong coincidence | `BHDiagonalConsequences.three_band_strong_coincidence` | Same-depth original marks, same selected letter, equal full prefix Parikh vectors |
| Strict-system exclusion | `BHDiagonalConsequences.three_band_no_strict_system` | Every finite nonempty closed noncoincident irreducible balanced-pair system is excluded |
| One-root assembly | `BHThreeBandClosure.family_closure` | All arithmetic, geometric and word-level conclusions concern one root and the original words |
| Finite complete carrier | `BHPisotFiniteBPA` | Actual Pisot contraction supplies a finite all-child closed strict-packet carrier for each finite seed |
| Full-factor termination | `BHThreeBandBPA.all_blocks_full_factor_coincidence` | Every irreducible balanced seed has finitely many actual iterate factors, and every factor reaches a singleton coincidence |

## Derivation: the diagonal recurrence

Use the literal tile lengths

\[
 \ell=(1,\beta,1+r/\beta).
\]

For the diagonal \(k=r\), put

\[
 A=\beta-r,\qquad B=r/\beta,\qquad
 Q(z,y)=Bz^2+Azy+y^2.
\]

A central packet has type \(1/1\), full displacement \((x,y,z)\), and
physical offset at most \(r-1\) in absolute value. Choosing the two
original positions in the runs realizes the reduced update
\((z,y)\mapsto(y,t)\) whenever

\[
 |t+Ay+Bz|\le (r-1)/\beta.
\]

The earlier literal realization theorem still computes the whole child
packet. Neither the admissibility choice nor the final path drops the
first coordinate \(x\).

### Outer reduction

The new proof uses the square-root-free cutoff

\[
 C=4(1+1/A)^2.
\]

It proves

\[
 Q(z,y)\ge\frac{81}{100}(z^2+y^2),\qquad
 C<\frac{81}{100}r^2.
\]

Thus \(Q(z,y)\le C\) places the integral pair strictly inside the
residual disk \(z^2+y^2<r^2\). When \(Q>C\), a proved rounding choice
gives an admissible digit with strictly smaller energy. The proof first
shows the zero endpoint and every point between zero and the exact
unrounded digit lower the energy. If rounding toward zero is inadmissible,
the alternative rounding has a controlled error that is absorbed above
\(C\). These facts are derived from the cubic identities, including
\(A^2=(1-B)(2+B)\); they are not numerical root estimates.

### Residual classification and short excursions

Inside the disk, the complete theorem gives one of three alternatives:
an admissible one-step energy decrease, the axis \(y=0\), or

\[
 r=3N,\qquad
 (z,y)\in\{(N-1,N),(N+2,-N),(1-N,-N),(-N-2,N)\}.
\]

The classification now derives all inequalities used by the earlier
congruence-elimination core. It does not ask its caller to provide an
arithmetic certificate. Integrality is essential to the congruence step.

Both exceptional shapes have actual two-edge excursions with lower final
energy. Swapping the original tracks and negating the full displacement
proves their opposite orientations. Axis packets have a labelled exit or
a shorter energy block, including the separate unit-axis excursion through
mixed-letter zero. Intermediate energy need not decrease; strict decrease
is required at the next central block endpoint. Mixed-letter zero remains
an intermediate state until equal labels are reached.

### Why this yields a finite path

A strict decrease of a real-valued function alone does not imply finite
termination. The formal proof instead establishes that an energy sublevel
contains only finitely many integer pairs \((z,y)\). Among central packets
reachable from the source with energy no larger than its initial energy,
choose a pair of minimal energy and retain a witness full packet and a
literal path to it. If that witness does not have a labelled exit, the
proved progress alternative reaches another central packet of strictly
smaller energy, contradicting minimality.

This argument does not assert that all full packets with arbitrary first
coordinate form a finite set. It needs only finitely many energy pairs and
the retained existential packet witnesses. The subsequent carrier argument
uses Pisot contraction separately; finite energy descent is not substituted
for that geometric finiteness claim.

## Derivation: entry from an arbitrary strict packet

The full entry proof is in
[the entry formalization note](bh-third-level-entry-formalization-2026-11-27.md).
It has four parts.

1. The existing occurrence-width theorem reaches an overlap containing
   more than half a unit of common physical length. Scaling by three
   substitutions then provides a common interval of length \(18\beta\).
2. Actual type-2 ancestry proves the required separation of bad starts.
   The third-level separation is \(\beta^3\), with both tracks handled
   independently and the original labels retained.
3. Three candidate windows of length \(4\beta\), spaced by \(7\beta\),
   cannot all be obstructed: a single track can obstruct at most one.
   The formal argument works with sets of bad starts, without assuming a
   finite enumeration or an attained extremum.
4. The clean-window locator finds actual type-1 marks in both substituted
   words. The terminal type-2 case moves to the next actual parent rather
   than inventing an out-of-range occurrence. Their positions give the
   central bound, and the reverse ancestry theorem recovers a composable
   path from the prescribed original packet.

The sign convention is explicit. If the original offset is \(D\), the
second physical track starts at \(S=-\beta^3D\). The difference of the
located physical starts is the negative of the assembled packet offset.
The source and target strictness inequalities therefore use the same
orientation as the actual digit update.

`run_family_entry_ordered` needs only the literal cubic scaling together
with the proved entry inequalities. `BHDiagonalAllSources` derives those
inequalities for each of the three bands and composes entry with the
appropriate central theorem. Its quantifier order is
\(\exists\beta\,\forall p\,\exists\text{ finite path}\). It does not
assert a single exit-depth bound for every integral packet or every
parameter. A finite carrier permits a maximum depth for that carrier.

## Actual arithmetic and word consequences

The incidence matrix and its positive square are

\[
 M=\begin{pmatrix}0&1&r\\1&k&1\\0&1&0\end{pmatrix},\qquad
 M^2=\begin{pmatrix}1&k+r&1\\k&k^2+2&k+r\\1&k&1\end{pmatrix}.
\]

The proofs compute these from the image words. They also compute
\(\det M=r\) and \(\chi_M=X^3-kX^2-2X-r\). Thus the theorem is
explicitly nonunimodular throughout its stated parameter range.

At the constructed root,

\[
 \chi_M(X)=(X-\beta)
 \left(X^2+(\beta-k)X+\frac r\beta\right).
\]

The remaining quadratic is positive on the real line. The unique real
root lies strictly between consecutive integers, so the monic cubic has
no integral root and hence no rational root. A cubic with no rational root
is irreducible over \(\mathbb Q\). The complex calculation proves more
than contraction: every other root is nonreal and has squared norm
\(r/\beta<1\). The positive left eigenvector is
\((\beta,\beta^2,\beta+r)=\beta\ell\).

For any source letters \(a,b\), the packet \((a,b,0)\) is strict because
all tile lengths are positive. Its literal exit has equal terminal labels
and full zero displacement. Expanding the ordered path into original
marks gives one depth \(n\) and decompositions

\[
 \sigma^n(a)=P\,c\,S,\qquad
 \sigma^n(b)=Q\,c\,T,\qquad \operatorname{Parikh}(P)=\operatorname{Parikh}(Q).
\]

This is the repository's established `StrongCoincidenceWitness`, rather
than a new weakened predicate. The existing strict-system theorem then
excludes each finite nonempty closed system of noncoincident irreducible
balanced pairs. That implication alone does not prove finiteness of an
arbitrary balanced-pair orbit.

The larger-domain arithmetic is also formalized. For every `4<=r<=k`,
`BHHigherDeterminantPisot.primitive_irreducible_pisot` constructs the root
and proves the same actual irreducibility and conjugate conclusions. Here
`A=(2+B)/beta`, so `A^2<9/beta^2<4*r/beta=4*B` proves the negative
discriminant without a near-diagonal assumption. This broadens the checked
arithmetic; the new all-source path theorem still has its three-band scope.

The arithmetic route and its prior-art boundary are recorded before code
in the [targeted source decision](bh-diagonal-arithmetic-stop-go-2026-11-27.md).
The rational-root and quadratic-factor method is standard; no novelty is
asserted for that method or for the general published spectral criteria.

## Verification and negative controls

### Finite BPA is derived separately from energy termination

`BHPisotFiniteBPA.terminates_of_pisot_all_source_exit` is a generic
three-letter implication. It assumes actual irreducible Pisot arithmetic,
positive image-scaling lengths and labelled exits from all strict packets.
It constructs the carrier before using the exit hypothesis.

The packet-to-overlap adapter sends `(top,bottom,delta)` to
`(top,bottom,-delta)`. This sign change reconciles the two existing offset
conventions and preserves the original two image marks. The actual positive
length row and contracting conjugates produce the existing `ContractionData`.
The existing finite-overlap-reachability theorem then bounds each complete
strict packet orbit. A finite seed has finitely many actual marks. Taking
the finite union of their complete forward orbits gives a finite carrier
that covers the seed and is closed under every literal strict child,
including children of coincidences.

The checked carrier-to-factor theorem now applies. The specialization
`BHThreeBandBPA.all_blocks_terminate` takes only the three natural parameter
bounds and an irreducible balanced seed. Its explicit full-iterate form
proves finiteness of

\[
 \{U:\exists n,\ U\in\operatorname{red}(\sigma^n(T_1),\sigma^n(T_2))\},
\]

and, for every such factor `U`, some iterate of `U` contains a literal
singleton coincidence in its reduction. Thus every distinct-letter swap
seed also terminates with coincidence. This removes the finite-carrier
formalization gap in the three-band spectral transfer. Property (F),
unimodularity and a prior balanced-factor bound are not assumptions of this
construction.

The generic implication retains its all-source exit hypothesis; it does
not prove that hypothesis for an arbitrary Pisot substitution. The three-band
specialization discharges it with `FamilyClosure`.

### Source replay

The [closure evidence packet](../evidence/bh-diagonal-closure-2026-11-27/README.md)
records the final source-isolated build, recursive axiom audit, native
exact replay, independent oracle and repository checks. Its exact counts
and hashes are the authoritative receipts. Earlier component receipts in
the residual packet remain unchanged historical evidence.

The dedicated gate is `tools/check_bh_diagonal_closure.sh`. It copies only
project source and configuration into a fresh workspace, validates pinned
dependency sources, reuses their upstream compiled cache, and rebuilds the
selected PSC dependency closure. It checks explicit theorem signatures and
the recursive axiom closure of all declarations in the new modules. Only
`propext`, `Classical.choice` and `Quot.sound` are allowed. This is a fresh
project-closure check, not a fresh build of all Mathlib or all PSC modules.

Native replay retains the seven-parameter diagonal residual test and the
third-level actual-window test. The independent Python oracle uses rational
root brackets and reconstructs the finite residual graph; it does not
import the native sign evaluator. Those finite checks test the executable
contracts; the universal parameter statement is warranted by Lean proofs.

The inherited negative controls remain live: projected zero is not full
integral zero; mixed-letter zero is not a coincidence; a saturated packet
need not remain central; fixed nearest rounding can have a genuine cycle;
the congruence integer cannot be replaced by an arbitrary real number;
shifted ordinals, forged certificates and exhausted budgets are rejected.
The finite-BPA bridge separately retains its expanding zero-hit control,
where zero displacement without equal labels fails to imply coincidence.

### Preserved contraction proofs and scoped dependencies

The finite-carrier assembly originally reached whole-Mathlib imports through
legacy spectral modules, exceeding the available cache capacity. The fix
extracts the existing length-functional block into `GeometricFLength` and
the existing contraction block into `GeometricFPisotCore`. The original
modules import these smaller modules and keep their earlier imports and
remaining proofs. All moved definitions and theorem bodies retain their
public names and exact source bytes; an independent comparison and the
extraction receipt record the 33-line and 267-line blocks. A small
characteristic-polynomial cast identity is restated in the core namespace.

The new consumer therefore uses the same contraction theorem through a
smaller dependency closure. This change does not narrow the environment of
the old consumers, edit vendored packages, or add an assumption. The combined
audit includes the extracted modules; their declaration counts are not
counts of newly invented mathematical results.

## Remaining obligations toward PSC

The completed three bands remove the open diagonal classification and
actual entry assembly from this family's Lean frontier. The remaining
universal obligations still require proofs for substitutions outside the
covered families: actual boundary hits on the prescribed cyclic
seed-reachable sources, residual one-sided aligned coincidence, and the
full nonunit geometric/spectral interfaces used by the chosen general
route. General C4 extraction and rank-two exclusion remain separate targets.

Published overlap-coincidence and balanced-pair criteria are used only with
their actual hypotheses. In particular, strong coincidence alone is not
treated as pure discrete spectrum, and a physical projection does not erase
the nonunit representation obligations. The spectral transfer note states
exactly which family conclusion follows in written mathematics and which
parts have not been formalized as a dynamical Lean theorem.
