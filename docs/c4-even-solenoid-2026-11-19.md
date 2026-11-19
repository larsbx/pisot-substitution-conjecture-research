# Unique halving on the nilpotent-parity solenoid

## Literature decision

Research base: `c0231e0fd64d9eee7f7bb798042d9966276e4cd6`.
Integrated main: `017969364269c116aaa5873bfcba6c9f1b1ba7e5` (#621).
This is a local
companion to the [unbounded-family investigation](c4-even-companion-family-2026-11-19.md)
and the already merged [even-stack residue](c4-even-stack-residue-2026-11-19.md).

**Proposed claim.** If the integer incidence matrix satisfies `M^3 = 2B`,
the inverse-limit solenoid of `M` has a unique half for every point. Its
coordinates are `H(z)_n = B z_(n+3)`. In particular this solenoid has no
nonzero point of order two. Test this statement on the actual solenoid
used by the geometric realization, rather than treating the degree-two
stack covering as an order-two translation of its base.

| Primary source | Transfer and boundary |
| --- | --- |
| [Baker–Barge–Kwapisz (2006), Definition 3.1 and Theorems 4.2, 5.1](https://www.numdam.org/article/AIF_2006__56_7_2213_0.pdf) | The geometric realization takes values in the inverse limit and describes the maximal equicontinuous factor under the stated hypotheses. The coordinate calculation itself uses no finite-fibre theorem. |
| [Barge (2015), Theorem 17 and Lemma 20](https://www.numdam.org/item/10.24033/bsmf.2691.pdf) | The stack has a double cover of its pure discrete factor; the deck map fixes the maximal equicontinuous image. It need not be a nonzero translation of the solenoid. Odd norm occurs in the mod-two eventual-rank bound. |
| [Barge–Kellendonk–Schmieding (2012), Corollary 3 and Theorem 5](https://arxiv.org/pdf/1204.1432) | The integral eigenfunction subgroup is saturated in first cohomology. This does not say that the pullback of an arbitrary degree-two covering has torsion-free cokernel. |
| [Barge–Bruin–Jones–Sadun (2012), Theorem 6](https://www.mat.univie.ac.at/~bruin/papers/HPC.pdf) | The norm-independent rank-two exclusion there is for homological degree one. It does not exclude the surviving fourth cohomology class of the cubic stack. |

**Decision: proceed with the coordinate theorem and retain a negative
control.** Nilpotent reduction modulo two gives an integer `B` with
`M^3 = 2B`; the proof may expose this factorization directly. The theorem
eliminates an order-two translation on the solenoid as an explanation of
the residual sheet exchange. It does not eliminate a covering acting
trivially on the solenoid. The integral-index control below shows why the
existing rank and winding data alone do not give that further conclusion.

## Work shown

### Assumptions and hypotheses

For the coordinate calculation, use the actual torus and solenoid from
`PeriodicPartnerRealization`. The torus maps `A,B` are additive
homomorphisms satisfying `AB=BA` and `A^3=2B`. A compatible sequence
satisfies `A z_(n+1)=z_n`. The integer-matrix bridge constructs `B` from
`(M mod 2)^3=0`, entry by entry, and proves commutativity from the integer
factorization. It does not assume the induced torus map is injective.

The integrated #621 proves compact Hausdorff topology on the target,
a shift homeomorphism and joint continuity of the target flow. The present
halving proof uses its unchanged algebraic solenoid definitions. It does
not establish continuity of realization or desubstitution from the ordinary
tiling hull, the normalized BBK/MEF identification, recognizability or finite
fibres. Those remain distinct inputs or obligations.

### Derivation / reduction

Define `H(z)_n=B z_(n+3)`. Commutativity makes `H(z)` compatible. Iterating
the compatibility relation three times gives

```text
2 H(z)_n = A^3 z_(n+3) = z_n,
H(2z)_n = B(2z_(n+3)) = z_n.
```

Thus doubling and `H` are inverse homomorphisms. In particular `2z=0`
forces `z=0`. This is a group-theoretic theorem on the constructed solenoid;
identifying that solenoid with a maximal equicontinuous factor still uses
the published realization hypotheses.

### Evidence and replay

The new
[Lean module](../proof/PscVerif/PscVerif/PeriodicPartnerEvenSolenoid.lean)
compiled successfully with Lean `4.34.0-rc2` on this local candidate.

| Declaration | Checked conclusion |
| --- | --- |
| `two_smul_half`, `half_two_smul`, `two_smul_bijective`, `no_two_torsion`, `unique_half` | The explicit coordinate half is both a left and a right inverse to doubling. |
| `half_shift` | Halving commutes with the existing solenoid shift. |
| `commutes_of_cube_eq_double`, `torus_factor_of_cube_eq_double` | The integer cube factor supplies the required commuting torus maps and equality. |
| `exists_cube_half_of_mod_two`, `incidence_mod_two_unique_halving` | Nilpotent reduced incidence directly implies unique halving and absence of nonzero order-two points on the actual realization solenoid. |
| `thueMorse_mod_two_cube`, `thueMorse_unique_halving` | The existing Thue–Morse incidence also has this base property, preserving the countercontrol. |

```sh
cd proof/PscVerif
lake build PscVerif.PeriodicPartnerEvenSolenoid
```

The initial module build completed successfully (`2074` dependency jobs,
with the new module compiled in `26` seconds on the local runtime). After
integrating #621, the focused build completed with `2206` dependency jobs;
the changed hull and realization modules and this module recompiled, the
latter in `2.0` seconds. The [integrated evidence packet](../evidence/even-rank-two-pr621-2026-11-19/README.md)
records that build and the complete source-bound axiom audit.
The main declaration takes only the displayed matrix hypothesis; it
does not take recognizability, finite fibres, coincidence rank or a stack
quotient as an input. The whole proposal's compiled axiom audit is
recorded separately with the final candidate acceptance. No new hosted
acceptance result is asserted.

### Negative controls

The Thue–Morse nilpotence and unique-halving controls are checked in Lean.
Its genuine double cover is the published control from Barge (2015),
Example 16 and Theorem 17; that cover is not formalized by this module.

The following is an algebraic consistency model, not a substitution or a
strict system. Let `E` be a torsion-free rank-three group with unique
halving, for example the direct-limit incidence group in the nilpotent
case. Set `H_X=H_Y=E direct-sum Z`, and define

```text
p*(e,n) = (e,2n),        N(e,n) = (2e,n).
```

Both composites are multiplication by two. The two rational ranks are
four, and the eigenfunction copies of `E` have torsion-free cokernel.
Nevertheless `coker p* = Z/2`. A base class `F=(0,1)` and a sheet class
`z=(0,1)` satisfy `p*F=2z`. The base winding can be one while the lifted
square winding is two. Embedding the extra `Z` as any primitive seam
class in `E direct-sum Z^l` also gives a primitive grouped-cycle map.

Consequently primitive grouped winding, unique halving of the eigenvalue
group, the transfer identities, and saturated eigenfunction injections
are jointly consistent with the index-two covering pullback. A new
geometric or literal-substitution constraint is needed to exclude it.

### Non-claims / remaining gaps

Unique halving does not contradict the deck involution of the stack
cover: that involution already acts trivially on the solenoid. No new
cohomological lower bound of five, explicit PIP3 strict counterexample,
or universal strict-system exclusion follows. The even nilpotent class,
higher coincidence ranks, universal C4 and PSC remain open.
