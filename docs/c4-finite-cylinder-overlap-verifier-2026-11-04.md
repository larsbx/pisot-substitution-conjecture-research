# A bounded finite-cylinder overlap verifier

**Status:** finite executable certificate and a written scoped enclosure
argument; independent human mathematical review pending. The measure
implications use [Corollary M3 and equation (11)](c4-nonunit-madic-counting-bridge-2026-11-04.md)
as written dependencies. No Lean verification of those implications, actual
strict Pisot component, or general C4 conclusion is supplied.

**Baseline:** PR [#494](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/494),
commit `6ee339c670e711eddc4bfbe43e8b0b9dbc2876ce`.
This work extends its cylinder target; it does not recompute the occupancy
bounds. The [targeted literature gate](c4-finite-cylinder-overlap-literature-gate-2026-11-04.md)
precedes implementation.

## 1. What this verifier establishes

The canonical Mojo producer retains every source letter, literal position,
following letter, proper-prefix Parikh vector, residue and parent residue.
It supplies a certified common Euclidean outer box and a rectangle for each
occurrence, then takes a complete hull in each letter/residue slice. The
independent Python verifier reconstructs the words, uses rational Gaussian
inversion for residues, and checks every outer rectangle against algebraic
affine corners.

There are two supported non-unit controls:

| ID | Substitution, in letter order 0,1,2 | Role |
| --- | --- | --- |
| 0 | `1 / 021 / 001` | PR #494 specimen; genuine finite residue separation for pairs involving letter 2 |
| 1 | `1 / 012 / 001` | Same incidence and Perron data, different word order and cylinder supports |

Both are productive controls with literal left strong-coincidence witnesses
for every pair. They are never admitted as examples of a strict system.
The supported cylinder depths are exactly `q=2,4,6`. Their complete
inventories contain **1,002 occurrences, 283 nonempty slices and 18 pair
upper bounds**, across both controls. These numbers describe the replay
scope, not an exhaustive census of Pisot substitutions.

The output is an upper certificate. A positive scalar supplied by a caller
does not become a cut density. Equation (11) additionally requires actual
complete strict words and a certified density in the same normalization.

## 2. Fixed hypotheses and normalization

Both substitutions have column incidence

```text
M = [[0,1,2], [1,1,1], [0,1,0]],
det M = 2,     chi(x) = x^3-x^2-2x-2.
```

The positive matrix `M^2`, the integer-root test and discriminant `-152`
establish primitive irreducible Pisot hypotheses: the sole real root
`beta` lies between 2 and 5/2, and the complex conjugates have squared
modulus `2/beta<1`. Each substitution has `sigma^2(0)` beginning with 0
and longer than one letter. We use its one-sided fixed point of period
`k=2`, so every implemented depth is a positive multiple of the period.

Choose physical lengths and stable quotient coordinates

```text
ell = (1, beta, beta^2-beta-1),
a = (beta+2)/beta^2 = (3 beta-beta^2)/2,
b = 1/beta = (beta^2-beta-2)/2,
W x = (x_0-a x_1, x_2-b x_1),
S(u,v) = (u,0,v).
```

The kernel of `W` is the Perron line. Consequently its restriction to the
contracting plane is a coordinate isomorphism. Exact polynomial identities
give `ell M=beta ell`, `W M=B W`, and

```text
B = W M S = [[-a,2-a],[-b,-b]],
kappa = abs(det [ell;W]) = a+beta+b(beta^2-beta-1)
      = 4 beta-beta^2 > 0.
```

Here area means ordinary coordinate area in the `W` chart, physical length
means `ell x`, and the compact M-adic Haar measure has total mass one.
Thus a depth-q cylinder weighs `2^-q`; the lattice covolume is `kappa`,
not one and not a differently normalized Euclidean determinant. Every
upper certificate rechecks this chart. A lower-density caller must use
cuts per unit of this physical length.

The formulas are not a general chart constructor for arbitrary incidence
matrices. An unsupported substitution is refused before a geometric result.

## 3. Certified Euclidean tails, not sampled point clouds

Let `R_c` be the Euclidean projections of the compact lifted prefix sets,
expressed in the `W` chart. Choose an even block length `m` and prove with
rational intervals that

```text
rho >= ||B^m||_infinity,       rho < 1,
T >= max ||W p(P)||_infinity
       over every occurrence sigma^m(d)=P c S.
```

If a rational `R>0` satisfies `rho R+T<=R`, then every `R_c` is contained
in `Q=[-R,R]^2`. To prove this, let `s` be the largest coordinate norm on
the union of the three compact sets. Their full block set equation gives
`s<=rho s+T`, hence `s<=T/(1-rho)<=R`. This uses boundedness and the
complete set equation; a finite prefix plot would not supply either bound.

The native producer certifies the digit bound by a complete prefix-hull
recursion. Starting with the singleton prefix zero, it forms the depth-n
hull for source d from every position `sigma(d)=P c S`, translating the
child's depth-(n-1) hull by `W M^(n-1) p(P)`. This is an exact finite-word
decomposition followed by a conservative interval hull. Repeated child
letters at different positions remain separate contributions.

The independent verifier checks the radius against all **55,583 literal
depth-12 digits per control**, using separate algebraic field arithmetic.
Its accepted block lengths are positive even integers at most twelve, with
a 100,000-symbol per-word cap; the canonical producer fixes block twelve.
Exceeding a cap refuses the certificate.

An explicit common calibration for both controls is
`m=12`, `rho=7/8`, `T=5`, `R=40`; the contraction and digit bounds
are checked rationally on the actual matrix and block digits, and
`(7/8)*40+5=40`. These simple constants are enclosure parameters, not
estimates of an actual subtile area.

For each actual depth-q occurrence, compute a rational outer rectangle

```text
E_(q,d,i) contains B^q Q + W p(sigma^q(d)[:i]).
```

Rational interval arithmetic and outward rounding supply the native
rectangles. The independent check evaluates all four affine corners in
`Q[beta]/(chi)` and proves that each lies in the supplied rectangle.
No floating-point comparison participates in acceptance.

## 4. Complete cylinder slices and the actual upper bound

For a prefix `p`, the native key is
`adj(M^q) p mod 2^q`. Equality of keys is precisely equality modulo
`M^q Z^3`. The independent oracle obtains the same class from the
fractional coordinates of `(M^q)^-1 p`, computed by Gaussian elimination.
This is not coordinatewise reduction of `p` modulo `2^q`.

The reduction from depth q to q-2 is recomputed from the same integer
prefix. Reducing the displayed key coordinatewise is generally wrong.
Independent enumeration verifies exactly `2^q` quotient classes, with
four refinements of each parent class between these even levels.

For every letter c and residue r, set

```text
B[c,r] = rectangular hull of all E_(q,d,i)
         with following letter c and residue r.
```

An empty slice has no contributing occurrence. The verifier does not
accept deleting a nonempty slice or one occurrence from its source list.
The exact slice formula (10) implies
`(R_hat_c)_r^(q) subset B[c,r]`. Therefore

```text
U_q(c,c') = 2^-q sum_r area(B[c,r] intersection B[c',r])
         >= mu(R_hat_c intersection R_hat_c').
```

All intersection areas and the final sum are rational and recomputed.
The cylinders are disjoint, so there is no extra factor for their number
and no omission of `2^-q`. Intersecting one hull per slice is deliberately
conservative; it preserves every occurrence, including repeated digits.

**A distinction from M3:** the exact compact sets `K^[q]` decrease.
Arbitrary enclosing rectangles at different depths need not decrease,
either as sets or in measure. The word-order control explicitly exhibits
an increasing hull bound between depths four and six. The scalar minimum
of any finite list of independently valid upper bounds is still a valid
upper bound. This does not prove that the hull method converges to the
true overlap or provide a rate.

## 5. Finite inequalities that really are available

For control 0, at depth two the complete nonempty residue supports are

| Letter | Keys in `Z^3/M^2 Z^3` |
| --- | --- |
| 0 | `(0,0,0)`, `(2,0,2)`, `(2,2,0)` |
| 1 | `(0,0,0)`, `(2,0,2)` |
| 2 | `(0,2,2)` |

Thus the complete slice formula gives the stronger set statements

```text
R_hat_0 intersection R_hat_2 = empty,
R_hat_1 intersection R_hat_2 = empty,
U_2(0,2) = U_2(1,2) = 0.
```

These are genuine finite-cylinder certificates for this productive
specimen. They are not generated by assuming a strict component. The
implemented deeper inventories preserve those two separations.

For pair `{0,1}`, both substitutions have an exact obstruction to any
residue-only separation. The first-letter map interchanges 0 and 1.
Consequently, at **every even depth**, `sigma^q(0)` starts with 0 and
`sigma^q(1)` starts with 1, both at the empty prefix. Residue zero therefore
survives on both sides. More strongly, the set equations contain
`A^(2n) R_hat_c subset R_hat_c` for c=0,1. Nonemptiness, compactness and
contraction give `0 in R_hat_0 intersection R_hat_1`.

Every implemented hull for this shared occurrence contains the same
nondegenerate affine image of Q. Its finite upper bound is positive.
The explicit strong-coincidence witnesses nevertheless imply a **null**
lifted overlap by the written equation (6) of the bridge. Nonempty and
positive measure are different claims. The bounded hull verifier does not
replace this analytic zero-measure argument.

For control 1 all three pairs share residues at the implemented depths.
The shared-class counts are `(3,1,2)`, `(12,4,8)`, `(48,16,32)` at
q=2,4,6, in pair order `{0,1}`, `{0,2}`, `{1,2}`. This demonstrates why
incidence data alone cannot determine which zero upper bounds hold.

The actual native packet, independently verified, gives these rational
upper bounds in the fixed coordinate/Haar normalization:

| Control | q | `U_q(0,1)` | `U_q(0,2)` | `U_q(1,2)` |
| --- | --- | --- | --- | --- |
| `1/021/001` | 2 | `4792739/1024` | `0` | `0` |
| `1/021/001` | 4 | `6856349/4096` | `0` | `0` |
| `1/021/001` | 6 | `23336309/16384` | `0` | `0` |
| `1/012/001` | 2 | `1797415/256` | `9275/4` | `2396867/512` |
| `1/012/001` | 4 | `16394203/4096` | `5412111/4096` | `10899051/4096` |
| `1/012/001` | 6 | `70053559/16384` | `23089531/16384` | `11630589/4096` |

The large positive values expose the loss in this conservative common-box
method. They are not tile areas, occupancy values or positive lower bounds
on overlap. All six control letter-pair overlaps are null by their explicit
strong-coincidence witnesses and the written bridge; the finite rectangles
only prove zero for the two residue-separated pairs in control 0.

## 6. A conservative, auditable lower-density input

A proposed positive density must come from actual literal words. First
validate a nonempty finite collection C of irreducible noncoincident
balanced pairs and its **complete** child factorization. Every occurrence
must have a target in C; a diagonal or escaped child refuses admission.
Track normalization may interchange the two words, but never deletes
child multiplicity.

Here is a useful finite sufficient premise, stronger than necessary and
independent of numerical Perron eigenvectors. For a selected pair e and
fixed integer t, verify that **every** source state has at least one
e-labelled descendant after exactly t generations. With `L_max` the
largest physical state length, every complete n-generation factorization
(n>=t) contains at least

```text
beta^(n-t) L_j/L_max
```

e-cuts: first factor at level n-t, then take one verified e-child from
each factor's t-generation descendants. These children occur in disjoint
parent factors. Dividing by `beta^n L_j` gives

```text
delta_e >= 1/(beta^t L_max)
        >= 1/(beta_upper^t L_max_upper) > 0.
```

The implementation uses a Boolean reachability recurrence for the
common-depth premise and recomputes the physical length bound in the
authenticated chart. It does not infer positive frequency from an
arbitrary matrix, an unphased SCC, an empirical ratio, or failure to find
a coincidence. An imprimitive component without this all-column premise
is refused by this v1 density method; the more general cyclic-frequency
theorem remains a separate possible extension.

The genuine constant-length strict control `012/120/201` has three
normalized rotation states, beta=3, `L_max=3`, and t=1, giving `1/9`.
It checks the literal density combinatorics only. Its singular reducible
incidence is outside the geometric verifier. A synthetic two-class cycle
is used only to ensure a missing common phase is rejected.

For the supported Pisot controls, every letter pair has a positive
strong-coincidence witness. Therefore no fully strict closed component
can supply this density input. The driver reports
`upper_only_no_strict_density` and never a contradiction.

## 7. Equation (11), acceptance and refusal

After both independent finite layers and their shared normalization have
passed, a sufficient exact comparison is

```text
U_q(e) < kappa_lower * delta_lower.
```

Use the **lower** endpoint of the certified covolume interval. Equality
does not pass. A scalar comparison helper is labelled arithmetic only;
the theorem-facing entry point also validates the upper packet, literal
component, common-depth coverage and density magnitude. In particular,
`U=0` plus an arbitrary positive number is rejected as an equation-(11)
certificate when the strict component is absent.

There is also a simple **necessary numerical screen** in this fixed chart.
All letter lengths are at least one: `ell_0=1`, `ell_1=beta>2`, and
`ell_2=beta^2-beta-1>1`. A noncoincident balanced state cannot have just
one symbol. Thus every strict factor has physical length at least two,
so its total cut density, and hence any one pair's certified lower
density, is at most `1/2`. Since

```text
kappa = 4-(beta-2)^2 < 4,
kappa delta_lower < 2,
```

equation (11) requires `U_q<2`. This is only a necessary condition. The
current common-box positive bounds are all greater than two; those
enclosures cannot finish equation (11) for **any** admissible strict-cut
density in the chosen normalization. The zero upper bounds pass this
numerical screen, but the productive controls still supply no strict
component. This separates an actual enclosure-resolution obstruction
from the independently missing density premise.

The adversarial suite covers:

- missing, duplicate and relabelled occurrences, including changes that
  preserve counts;
- coordinatewise residues and incorrect refinement of displayed keys;
- a sampled point used as an outer box, a too-small invariant radius,
  noncontracting blocks, reversed boxes and incomplete slice hulls;
- wrong Haar weights, incompatible physical units and enlarged covolumes;
- unsupported density labels, missing literal components, coincident or
  reducible states, and omitted children;
- a phase-sensitive synthetic matrix, false coincidence witnesses,
  unsupported substitutions, wrong periods and budget exhaustion.

All refusals mean that no certificate is returned. They are not evidence
of noncoincidence, a counterexample or positive overlap.

## 8. Reproduction, proposed changes and remaining gap

The complete commands, outputs and source digests are in the
[evidence packet](../evidence/c4-finite-cylinder-overlap-2026-11-04/README.md).
The ordinary replay is:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_finite_cylinder_overlap.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_cylinder_density.mojo)
(cd kernel && pixi run --locked mojo run -I . c4_finite_cylinder_overlap.mojo) > /tmp/cylinder.txt
PSC_CYLINDER_NATIVE_OUTPUT=/tmp/cylinder.txt python tests/test_c4_finite_cylinder_overlap_oracle.py
python oracles/python/c4_finite_cylinder_overlap.py /tmp/cylinder.txt
```

The optional density-input interface is deliberately exercised with an
[invalid empty-component record](../evidence/c4-finite-cylinder-overlap-2026-11-04/rejected-empty-strict-component.json):

```bash
python oracles/python/c4_finite_cylinder_overlap.py /tmp/cylinder.txt \
  --density-input evidence/c4-finite-cylinder-overlap-2026-11-04/rejected-empty-strict-component.json
```

This command must return nonzero with a strict-state-count refusal, even
though it selects a certified zero upper bound and supplies the positive
number `1/100`. The record is an adversarial input, not a strict system.
The same rejection is exercised under `python -O`; no theorem-facing
guard relies on Python's removable `assert` statement.

Without native output, the standalone Python calibration and adversarial
tests run, but the native comparison is explicitly skipped. That skip
cannot be presented as native validation. The focused hosted workflow
requires the canonical output and independent replay.

The new finite result is useful: complete residue supports can prove
actual empty lifted intersections, and the verifier now checks rational
Euclidean upper bounds with authenticated occurrence provenance. It also
records a reproducible obstruction for the remaining control pair:
residue zero persists, the chosen finite hull bounds remain positive,
and no strict-density premise is available.

The unresolved general task remains an upper bound below the positive
density of a **represented unwitnessed pair in an actual strict system**,
or a theorem excluding all such systems with its hypotheses proved.
Complete unions of shrinking occurrence boxes, separate geometric and
residue depths, or a justified finite overlap automaton may strengthen
the upper side; this contribution does not assume their success.

Finite replay, the written enclosure/counting proof, pending independent
human review, and general C4/G1/BH/A1'/PSC status are separate. No governed
claim is promoted by this contribution. Repository changes are proposed
for review; no merge is part of this task.
