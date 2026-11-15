# C4 image scaling and finite overlap subinvariance

## Assumptions and hypotheses

The source base is #547 head `e1033f3d9b5fc9c9424d10e12f0e44b63135be03`,
tree `e92921435a5230d7f96d62730cc6c9fe64116630`. The compact argument
uses the original compatible tuples in the quotients by `range (M^q)`.
The range computation assumes that the integral action is injective. The
Haar computation additionally uses a finite free integral module and a
normalized additive Haar measure on the resulting compact group. The named
product uses Lebesgue measure in the actual stable chart. The history
application uses the existing full and nondiagonal finite carriers, their
literal marked histories, and only the even block powers admitted by the
actual period-two words.

## Derivation / reduction

For a compatible tuple `x` with first residue zero, pick an integral
representative `w_q` of its coordinate at depth `q+1`. Reduction to depth
one gives `w_q = M z_q` for some integral `z_q`. Replacing the
representative changes `M z_q` by an element of `M^(q+1)V`. Integral
injectivity cancels the leading `M`, so the class of `z_q` modulo
`M^q V` is well-defined. The same cancellation proves that these divided
classes are compatible. Their tuple maps to `x`. The forward inclusion is
the depth-one annihilation lemma. Since evaluation is onto by the integral
star map, the action cokernel is the actual first quotient.

The action is a closed embedding by compactness and injectivity. Its image
is open because it is a fiber of the continuous first evaluation with
discrete codomain. Translation by an integral lift permutes the first-residue
fibers transitively, so normalized Haar assigns each mass `1 / |Q_1|`.
Comap by the action is Haar since this is an open embedding of additive
groups. Uniqueness and evaluation on the whole compact group give the same
factor on every image. For the named matrix the integral quotient
cardinality is the absolute determinant, namely two. An independent
integer check is that `M(u,v,w) = (v+2w,u+v+w,v)`. A vector `(a,b,c)`
has an integral preimage exactly when `a-c` is even. Then
`v=c`, `w=(a-c)/2`, and `u=b-c-w`.

On the stable plane the determinant is `2b = 2/β > 0`. The image of
the unit square times the entire compact group therefore has product
measure `(2/β)(1/2) = 1/β`. Haar uniqueness extends this product scaling
from the reference rectangle to every set. Translation preserves measure,
and iteration gives `β^(-k)` for any affine image with linear part `T^k`.

For a depth-`n` literal history at block power `k = 2r`, the measure of
its exact compact piece is `β^(-kn)` times its terminal overlap measure.
Thus for each admitted packet `p` the finite cover yields
`μ(O(p)) ≤ β^(-kn) Σ_h μ(O(target(h)))`.
The sum is over the full literal histories of the chosen carrier. In
particular, two histories ending at the same packet still contribute two
terms. For finite overlap measures and depth one this is the subinvariant
recurrence in the orientation of `OverlapContraction.recurrence_of_cover`.

## Evidence and replay

The original sources and the literature scope are linked in the
[pre-code review](c4-madic-haar-literature-2026-11-11.md).

The exact #547 revision has a successful generated-source check and
cut-pair replay, with the [complete overlap Lean audit](https://github.com/larsbx/pisot-substitution-conjecture-research/actions/runs/43080502504)
still queued at inspection. The cover layer of this increment is a
candidate dependency on that exact source. The local range, cokernel and general compact-Haar modules compiled against
the pinned Lean toolchain. The finite controls passed on Mojo
1.1.0.dev2026090805 and the independent Python oracle. The combined isolated
Lean audit remains outstanding.

```bash
./tools/check_lean.sh
python tools/make_proof_bank.py --check
python -m pytest -q tests/test_c4_madic_residue_oracle.py -k half_index
(cd kernel && pixi run mojo run -I . tests/test_c4_madic_residue.mojo)
```

## Negative controls

For both named matrices, the finite depth-one through depth-four actions
have image/total cardinalities `1/2, 2/4, 4/8, 8/16`. Each image class
has a unique divided class one level lower. The finite actions themselves
have collisions, including the depth-two collision of classes 0 and 2.
A cover with two occurrences of the same image has union mass `1/2` and
occurrence-sum mass 1 under normalized counting measure. This is a
counterexample to deriving equality solely from completeness of a cover.

## Non-claims / remaining gaps

The bound requires no measure disjointness. Equality, an occurrence-count
rate gap or loss on the actual finite domains, and positive measure for an
appropriate strict source require further arguments. The compact group is
used directly. No equivalence with a number-field completion product or
promotion of C4, G1, or general PSC is asserted.
