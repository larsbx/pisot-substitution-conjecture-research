# Actual matrix-adic carrier and residue bridge: literature stop/go gate

**Decision (2026-11-11): proceed with the algebraic inverse-limit carrier,
its exact first-residue test, and conditional tile-profile enclosures.**
This gate is recorded before the new Lean, canonical Mojo, and oracle
implementation. It permits the explicitly stated constructions below. It
does not authenticate a Rauzy tile realization or promote C4, global G1,
Concentration, or general PSC.

The starting source is PR #540 head
`42ab08d3e012dd13dbd6d40179c8db9420c79f70`. The earlier
[compact matrix-adic counting bridge](c4-nonunit-madic-counting-bridge-2026-11-04.md)
contains written arguments for a richer geometric construction. This step
formalizes a smaller algebraic part and the conditional residue bridge;
it does not silently treat the remaining written geometry or measure
arguments as established Lean results.

## 1. Question and inspected context

Can the abstract residue premises of
`OccurrenceCover.reflectsIntegralRange_of_residue` be discharged by an
actual inverse limit, instead of being assumed? Can complete finite
occurrence tables then give sound tile-support exclusions when a literal
tile equation in that carrier is supplied?

The review read `AGENTS.md`, the relevant entries in
[the side-notes ledger](side-notes-ledger.md), the November 4 bridge and
[occupancy certificate](c4-nonunit-residue-occupancy-2026-11-04.md), and the
current `OccurrencePiece`, `OccurrenceCover`, and `OccurrenceAdmissibility`
interfaces. The ledger's column-lattice correction is essential:
`M^q Z^3` denotes the image of the column action, not the row span of a
row-major array. The existing local-admissibility work also requires a
distinction between exact occurrence indices and their projected set
supports, and between an authenticated compact module and an unrestricted
product of completion fields.

## 2. Primary sources inspected

| Primary source | Specific material inspected | Use and transfer boundary |
| --- | --- | --- |
| [Minervino--Thuswaldner, *The geometry of non-unit Pisot substitutions*](https://arxiv.org/pdf/1402.2002), Section 3, Proposition 8.1, Theorem 8.3(i) | Completion-field representation space; bounded finite-place support derived from prefix expansions; prefix-indexed tile equation. | The paper supplies the geometric context and shows why support authentication matters. Its full field product is not identified with the compact integral inverse limit constructed here. Its Haar and tiling theorems are not imported. |
| [Stacks Project, Lemma 5.22.2, tag 08ZY](https://stacks.math.columbia.edu/tag/08ZY), and [Lemma 5.22.4, tag 08ZZ](https://stacks.math.columbia.edu/tag/08ZZ) | Inverse limits of finite discrete spaces are compact Hausdorff and totally disconnected; finite clopen refinements arise at a common level. | These results explain the finite-quotient topological extension. They do not show that an arbitrary algebraic quotient is finite, that a selected support is a tile, or that a bounded computation exhausts an infinite geometric object. |
| Mathlib at pinned revision `4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09`: [quotient definitions](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Quotient/Defs.lean), [quotient maps](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/LinearAlgebra/Quotient/Basic.lean), and [cofiltered profinite limits](https://github.com/leanprover-community/mathlib4/blob/4edb0dbaa3b3cf729d86d1e2f035474d5ae2ac09/Mathlib/Topology/Category/Profinite/CofilteredLimit.lean) | Actual locally installed source for `Submodule.Quotient.mk_eq_zero`, quotient surjectivity, `Submodule.mapQ`, `mapQ_apply`, and cofiltered-limit support lemmas; also the [official quotient documentation](https://leanprover-community.github.io/mathlib4_docs/Mathlib/LinearAlgebra/Quotient/Defs.html). | Existing quotient infrastructure supports a direct compatible-sequence construction. The pinned source, rather than a guessed theorem name or current documentation version, is the implementation authority. No existing library theorem is claimed to authenticate the repository's tiles. |

This is established inverse-limit and quotient machinery. The contribution
is its explicit formal connection to this repository's occurrence-cover
interfaces and bounded certificates. The algebraic arguments in the next
sections are the proposed derivations, not claims that the papers already
contain this exact Lean interface.

## 3. Algebraic construction and exact hypotheses

Let `V` be an additive commutative group with its integer-module structure,
and let `M : V -> V` be an integer-linear endomorphism. Define

\[
L_q=\operatorname{range}(M^q),\qquad Q_q=V/L_q,
\qquad
H_M=\{(x_q)_q\in\prod_qQ_q:\ r_q(x_{q+1})=x_q\},
\]

where `r_q` is induced by the identity on `V`. The inclusion
`L_(q+1) <= L_q` makes it well defined. `Q_0` is trivial. Define
`star(z)_q = z mod L_q`, evaluation `rho_q(x)=x_q`, and `A` by the
endomorphism induced by `M` at each level. Compatibility follows from
commuting reduction and multiplication. Each is an additive map, and

\[
A\,\operatorname{star}(z)=\operatorname{star}(Mz).
\]

Neither injectivity of `M`, finiteness of a quotient, a topology, nor a
tile hypothesis is needed for these definitions or for

\[
\rho_1(Ax)=0,
\qquad
\rho_1(\operatorname{star}(z))=0
\ \Longleftrightarrow\ z\in MV
\ \Longleftrightarrow\ \exists y,\ My=z.                 \tag{1}
\]

The first equality follows because a representative `Mu` belongs to
`MV`; the equivalence is the exact kernel property of the quotient.
Consequently `Ax=star(z)` implies an integral preimage of `z` when
`V=Z^3`. The converse follows by applying `star` to such a preimage.
This discharges range reflection on this carrier without assuming it.

### Injectivity belongs to the inverse-limit action

If `M` is injective, then `A` is injective. To prove its kernel trivial,
take a representative `u` of `x_(q+1)`. From `Ax=0`, one obtains
`Mu in M^(q+1)V`. Write `Mu=M(M^qv)` and cancel `M`; hence
`u in M^qV`. Compatibility implies `x_q=0`. This works for every `q`.
The argument uses the next level and makes no finite-index assumption.

The stronger equality `range A = ker rho_1` is also justified under
injectivity of `M`: for a compatible sequence with zero first residue,
choose a level-`q+1` representative in `MV`, divide by `M`, and reduce
modulo `M^qV`. Injectivity makes this independent of the representative
and makes the divided residues compatible. It is an optional extension,
not needed for the first-residue cover bridge.

Do not infer that `star` is injective. Its kernel is
`intersection_q M^qV`. For `M=diag(2,1,1)` on `Z^3`, the last two
coordinate axes are in this kernel. For an invertible integer matrix all
the quotients, and hence `H_M`, are trivial.

### Topology is a separate layer

The algebraic construction is meaningful even when some `Q_q` is
infinite. If every quotient is finite and given the discrete topology,
the compatible sequences form a closed subset of their compact product;
this gives a compact Hausdorff group. For a nonsingular integer matrix,
finiteness follows from the finite index of its image lattice. A formal
compactness claim must prove or assume this finiteness and install the
appropriate topology. The algebraic module alone is not a Haar-measure
construction.

## 4. Bridge to the supplied occurrence model

The same detector works on `E x H_M`, with additive maps `B` on `E`
and `pi : Z^3 -> E` satisfying `B(pi z)=pi(Mz)`. Put
`A_EH(e,h)=(B e,A h)` and `star_EH(z)=(pi z,star z)`; first residue
ignores `E`. Formula (1) proves range reflection for this product. To use
the existing inverse-piece equality and history-cover theorems, also
supply injectivity of `B` and `M`, the literal tile equation, and the
other premises of those theorems. No injectivity of `pi` or of the
combined star map is needed for this argument.

For a fixed block depth `q`, the quotient calculation gives
`rho_q(A_EH^q x)=0`. Suppose the supplied sets obey the complete literal
block equation

\[
K_c=\bigcup_{\sigma^q(a)=P c S}
       \bigl(A_{EH}^{q}K_a+\operatorname{star}_{EH}(\pi_{\!P})\bigr),
\]

where `pi_P` here denotes the integer Parikh vector of `P`. Then

\[
\rho_q(K_c)\ \subseteq\
C_{c,q}:=\{\pi_{\!P}\bmod M^q\mathbb Z^3:
                    \sigma^q(a)=P c S\}.                 \tag{2}
\]

This enclosure needs no compactness, nonemptiness, disjointness, or
measure assumption: evaluate a witnessed member of a union piece. An
exact one-step tile equation can support the block equation by iteration,
but the formal bridge must either prove that iteration with literal
addresses or take the displayed block equation as an explicit premise.
Equality in (2) follows if every contributing ancestor tile is nonempty;
without that premise an empty tile may contribute a listed digit and
strictly enlarge the outer profile.

At any fixed depth, reducing the two sides of an overlap or paired
occurrence to these authenticated profiles gives a sound emptiness test:
disjoint projected outer supports imply an empty actual intersection.
Intersecting profiles do not prove a genuine overlap, let alone positive
overlap measure. A finite packet restriction is complete only after every
omitted actual inverse piece is shown empty or covered by retained pieces,
as stated in the existing exact retained-union criterion.

The support sets in (2) may deduplicate equal residues for set containment.
The underlying occurrence table must still retain every parent letter,
selected position, prefix, selected letter, suffix, and multiplicity.
Equal residues are not equal occurrences. All paired-mark and history
counting continues to use the literal occurrence indices.

## 5. Finite certificate scope and mandatory controls

The canonical Mojo certificate and independent integer oracle may check
complete finite quotients, their group operations and reductions, induced
matrix actions, literal block occurrences, residue profiles, and finite
exclusions. A bounded traversal must certify that all quotient classes
were enumerated; hitting a cap or an arithmetic refusal is inconclusive.
Use exact column-lattice membership. A conservation identity alone does
not certify either quotient completeness or correct word addresses.

The following controls belong in the implementation design:

- **Noncyclic quotient:** for `1/021/001`, the depth-two matrix is
  `[[1,3,1],[1,3,3],[1,1,1]]`, with quotient invariants `(1,2,2)`.
  Its four-element quotient is `Z/2 x Z/2`, not `Z/4`. Certify its
  operation and reduction tables rather than infer a cyclic group from
  the determinant. The earlier complete literal table supplies a useful
  independent regression, not permission to reuse its implementation as
  the new oracle.
- **Finite action versus limit action:** multiplication by `2` on
  `Z/2^q` has a nontrivial kernel for positive `q`, although its action on
  the full compatible inverse limit is injective. No finite-level
  action-injectivity assertion may replace the next-level proof.
- **Unit and singular controls:** unit incidence gives trivial residues
  and no residue exclusion power. A singular endomorphism still admits
  the algebraic first-residue test but does not inherit action
  injectivity or finite quotients. Singular occurrence-lift witnesses
  from the predecessor remain valid warnings against choosing one lift
  and claiming that every lift was represented.
- **Unrestricted-field control:** multiplication by a nonzero scalar on
  a product of characteristic-zero completion fields is surjective.
  For a non-surjective integral incidence action, global range
  reflection there is false. Also every additive homomorphism from a
  divisible group to a finite group is zero. Formula (1) is a fact about
  `H_M`, and about products using that factor, not a global residue map
  on the full completion-field product.
- **Mandatory forward leak:** preserve the existing `00/11/22` control
  with `S={(0,1,0),(1,0,0)}`. Each source has four forward positional
  pairs: one retained positive pair, one positive exit, and two further
  outside pairs with zero mass under the original physical calibration.
  Across both sources the positive-pair receipt is
  `full=4, retained=2, positive_exits=2`. These are physical-length
  diagnostics, not compact-overlap Haar measures. The supplied domain is
  inverse-closed. Range reflection or incoming coverage cannot turn this
  into forward completeness or authorize deletion of the positive exits.
- **Support versus occurrence:** repeated marks with the same projected
  residue must remain separate records. Incomplete prefix sampling,
  arbitrary coordinate caps, and a nonempty projected intersection
  cannot serve as geometric certificates.

## 6. Go / narrow / stop and the next missing lemma

**Go:** build the actual coherent quotient carrier; prove its additive
maps and exact first-residue facts; prove the inverse-limit action
injective under integral injectivity; instantiate the existing range
reflection interface; and prove conditional block-profile enclosures and
their sound exclusion consequences. Run canonical Mojo and independent
integer checks for the declared bounded claims, preserving literal
addresses and multiplicities.

**Narrow:** topology, finite-index proofs, compactness, `range A = ker
rho_1`, and equality of profiles are separate results with the premises
above. Include them only when actually proved. Finite certificates do not
certify an infinite coherent state merely by listing finitely many of its
residues, and no executable result substitutes for the conditional Lean
tile equation.

**Stop at the authentic-realization boundary:** the minimal missing
geometric bridge for applying the new detector to the intended compact
overlaps is a realization lemma giving the actual sets `K_a` in the
chosen `E x H_M`, the correct translation and action maps, and their
complete literal occurrence tile equation. An alternative sufficient
route for residue exclusions is an authenticated additive map from an
independently defined geometric model that intertwines the action and
integer translations and supplies the necessary support enclosures; the
original model's complete literal tile equation remains an explicit
premise for incoming-cover conclusions. A bare finite residue table
supplies none of that data.

After this realization, residue exclusions can become genuine geometric
exclusions. They still do not by themselves establish a complete finite
packet domain, stable-coordinate bounds, product-Haar scaling, or the
positive compact overlap measure forced by a strict cut root. Those
remain separate obligations. Physical interval length is not compact
overlap measure, and no general PSC closure follows from this stage.
