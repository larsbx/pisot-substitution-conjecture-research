# The return-word boundary term in C4 winding

The [marked-count argument](c4-homoclinic-winding-counts-2026-11-20.md)
locates the odd winding in a joint contribution of the original seam
rays. The proper rewrite carries this contribution in an integral
fixed vector of return-word counts. Adjacent-pair counts recover the
original seam coefficients, even though flattening to original letter
counts kills the vector. The stack projection reads it by counting
which inflated stack tiles contain a vertex of their twin. See the
[literature decision](c4-return-seam-boundary-stop-go-2026-11-20.md).

## Work shown

### Assumptions and hypotheses

Use a primitive aperiodic substitution and a common inflation power
fixing the original periodic seam graph. A seam `(a,b)` has last left
letter `a` and first right letter `b`. Its entire left ray depends on
`a`, and its right ray on `b`. Choose an allowed periodic cut `e₀` as
the proper return marker and orient every graph edge from left to right.
An integer seam cycle `W` has zero row and column sums, with zero weight
on absent seams. Denote the return incidence by `R`, the original
incidence at this power by `M`, and the letter-count flattening by `P`.

For the dimension statement use irreducible cubic Pisot incidence. For
the winding statement also use the [even stack reduction](c4-even-stack-residue-2026-11-19.md),
with ordered stack quotient `X`, unordered factor `Y`, and grouped seam
tilings `Qᵢⱼ`. Number the groups so that group zero on each side is a
singleton and choose their seam as `e₀`. A simple cycle of weight one at
`e₀` exists by the [singleton-edge argument](c4-homoclinic-winding-counts-2026-11-20.md#two-checks-on-the-original-to-quotient-transfer).

### Derivation / reduction

#### The signed return vector retains the whole seam cycle

On the tiling of `(a,b)`, take the nearest strictly negative return
marker `lₐ` and the nearest strictly positive one `r_b`. The two cuts
depend only on their respective original rays. Write `Uₐ V_b` for the
original patch between them, split at zero, and `Cₐ_b` for its return
word count column. The patch contains one return word when `(a,b) ≠ e₀`.
At `e₀` the origin is a marker and the patch contains two return words.
Define the signed column

```text
D_R(W) = ∑ₐ ∑_b Wₐ_b Cₐ_b.
```

The common inflation power preserves every marker cut and fixes the
seam tilings. Inflation of `[lₐ,r_b]` moves both ends outwards. The
additional return words on the left depend only on `a`, and those on
the right only on `b`. Hence the row and column sums cancel both pads
and give `R D_R(W) = D_R(W)`. The flattened patch count is exactly
the sum of the counts of `Uₐ` and `V_b`. The same cancellation gives
`P D_R(W) = 0`. These two conclusions are independent of parity.

For any original legal adjacent pair `e`, define a row `Γ_e` on a
return word by counting occurrences inside the word and adding one if
`e = e₀` for the marker at its left end. Count inside each return word
and join the results. Every actual interior cut is counted once, with
the prescribed extra marker at the left end of the patch. Splitting
the original patch at zero gives

```text
Γ_e Cₐ_b = count_e(Uₐ) + count_e(V_b) + [e = e₀] + [(a,b) = e].
Γ_e D_R(W) = W_e.
```

Thus adjacent-pair counts recover all cycle coefficients over the
integers. In particular, `Γ_e₀` is the total return word count row,
and it takes value one on the unit cycle. That cycle is primitive
and survives reduction modulo every integer greater than one.

The flattening also forgets a corresponding literal loop. For the
unit simple cycle with successive left vertices `a_i` and right
vertices `b_i`, use the free group on return words. Let `Bₐ_b` be the
ordered central return word list with count `Cₐ_b`. The loop is the
product of `B_(a_i,b_i) B_(a_(i+1),b_i)⁻¹`, in cycle order. Flattening
gives `U_(a_i) U_(a_(i+1))⁻¹` in each factor, so the product is the
identity. Inflation sends `Bₐ_b` to `Lₐ Bₐ_b S_b` with the same side
pads as above. In the product each right pad cancels with its inverse
and the left pads telescope, leaving conjugation by the initial left
pad. The central loop is nontrivial in the return-word group since
its abelianization has marker count one.

#### The fixed lattice in the cubic rewrite

The [eventual-range sequence](https://arxiv.org/pdf/math/0702669)
shows that the rational first cohomology has the eigenvalues of `M`
and one fixed dimension for each independent seam cycle. More
explicitly, the reduced `H⁰` of the eventual range maps injectively
to the eventual letter-count space. This map is equivariant after
the common power. Its domain is fixed and the Pisot incidence has
no eigenvalue one, so the domain is zero. The remaining succession
of letter counts and graph cohomology is exact. Since `M−I` is
invertible over the rationals, the graph quotient contributes a
semisimple fixed space. The proper rewrite conjugates this inflation
action and its first cohomology is the eventual transpose of `R`.
Consequently the rational dimension of `Fix(R)` is the cycle rank.

The map `D_R` is injective by the `Γ_e` rows and has the full
rational rank. Any integral fixed column is therefore `D_R(W)`
for a rational cycle `W`. Its `Γ_e` values are integers, so `W`
is integral. The fixed lattice is exactly the seam-cycle image.

If `M` is nilpotent modulo two, the quotient by this fixed lattice
is free with characteristic polynomial `t^q χ_M(t)` for some
nonnegative `q`. If `d` is the rank of this free quotient,
Cayley–Hamilton modulo two puts its `d`-th image in twice the
quotient. The `dk`-th image lies in `2^k` times the quotient.
The eventual image of `R` modulo `2^k` is thus exactly the reduction
of `D_R` on integer seam cycles. The original nilpotence removes
the original letter-count part and leaves this fixed return lattice.

#### Which stack vertices contribute to the winding

In Barge's proper stack substitution twins have disjoint vertex
sets. If they shared a vertex, properness
would put the same inflated final tile at its left and the same
inflated first tile at its right after substitution. This contradicts
the disjointness of the twin tilings at every inflation level. The
ordered-pair tiling is formed from their intersections, so each
ordered-pair vertex belongs to exactly one of the underlying stacks.
Inflation about such a vertex puts the owning stack on the unique
proper periodic seam. The two eventual ordered seam bits in the
[sheet phase construction](c4-even-stack-residue-2026-11-19.md#the-cover-requires-four-classes-on-its-base)
are therefore precisely these vertex owners. Choose bit zero for
a vertex in the first stack. The unordered tile is marked exactly
when ownership changes across it.

In a single first-stack tile, both endpoints have owner zero. All
vertices strictly inside it have owner one. If there is an interior
vertex, ownership changes twice. If there is none, it never changes.
Thus the odd phase `z` makes exactly one full turn across that stack
tile when its interior contains a twin vertex, and zero otherwise.
The descended square `F` makes twice that increment. In the chosen
marker seam group, `Q₀₀` has a stack vertex at zero. Its twin `Q₁₁`
has none there. The other unordered tiling is periodic with an
interior origin by uniqueness of the proper periodic vertex tiling,
so `Q₀₁` and `Q₁₀` also have interior origins. The actual stack
projection therefore retains the original vertex at zero in exactly
one of the four groups.

The return-to-stack map is a length-preserving subdivision of each
return word, with stack count matrix `C`. Take a sufficiently high
inflation power `k` and let `η_k(t)` be the number of small stack
tiles in the inflated image of stack tile `t` that contain a twin
vertex in their interior. The value is independent of the tiling
containing `t` once `k` is large enough. Indeed, the inflated tile
and fixed proper prefix and suffix of its neighbours give common
strips growing on both sides. By uniform continuity of `z` on the
compact hull, agreement on a sufficiently large fixed window
gives phase difference less than a quarter turn. For large enough
`k` the two inflated paths are this close throughout the tile.
They agree at both endpoints, which are first-stack vertices.
Their difference has a unique small continuous real lift with
zero at both ends. The paths have equal integral winding, which
is exactly the vertex count defining `η_k`. Choosing one such path
per tile gives a circle map on the wedge of stack tiles because
all endpoints have value one. The actual inflated phase differs
from this map by a continuous small real lift, so `η_k` also
represents its integral class at that stage.

Let `K` be the odd marked-count difference for the common finite
quotient patch of the two bi-asymptotic tilings `A,B`. Take `k`
large enough that all the inflated original marker endpoints lie
beyond that patch. On the inflated marker interval for each seam,
the marked count is `2 η_k C Cₐ_b`. The additional counts outside
the common quotient interval are determined by the corresponding
original endpoint, since `A,B` agree exactly on both tails. They
cancel in the signed sum. In the common interval there is a
diagonal value and an off-diagonal value differing by `K`. Their
weighted sum is `2K W_e₀`, since the zero groups are singletons.
This gives the integral identity

```text
η_k C D_R(W) = K W_e₀.
```

Hence the modulo-four contribution of `F` is `2 W_e₀`, or twice
the raw occurrence of the chosen marker at the seam, after removal
of independent left and right counts. This identifies the actual
joint term using the proper return words and the stack vertices.
On the unit cycle it is nonzero already modulo four. The
stack-count vector `C D_R(W)` is fixed by the stack incidence and
is nonzero modulo two, since its `η_k` readout is odd.

The full stack count vector on each cycle is also determined. In
the even reduction the covering pullback from `Y` to `X` is an
equivariant rational isomorphism. Their common nonzero spectrum
has polynomial `χ_M(t)(t−1)`. The stack presentation is proper,
so the fixed space of its incidence has dimension one. Let `W*`
be the unit cycle. The row `η_k` is nonzero on the fixed space,
as its value on `C D_R(W*)` is `K`. Consequently the integral
vectors satisfy

```text
C D_R(W) = W_e₀ C D_R(W*).
```

The stack projection keeps exactly the singleton-edge coefficient
of the seam cycle. The integer multiple of a primitive stack fixed
vector appearing here is odd. Under original nilpotence its
reduction therefore generates the eventual stack count image
modulo `2^k` for every `k ≥ 1`, by the same quotient argument.

Equivalently, the pullback of the marked circle class to the
original hull equals twice the return-marker class in first
cohomology modulo four. To see that the cycle readouts suffice,
use the proper return presentation. Its cohomology with these
coefficients is the direct limit under `Rᵗ` modulo four. Restriction
to the fixed return lattice is onto since that lattice is saturated.
A row restricting to zero dies on iteration, since the eventual
count image modulo four is exactly that lattice's reduction. The
row for the pulled-back square phase has readout `2K Γ_e₀` on it,
and the marker class is represented by the total return count row
`Γ_e₀`. Inflation leaves all these fixed-vector readouts unchanged.

### Evidence and replay

| Lean endpoint | Verified implication |
| --- | --- |
| `seam_sum_fixed_of_side_padding` | Side pads cancel and leave an integral fixed column |
| `seam_sum_map_zero_of_side_terms` | Independent left and right raw letter counts cancel |
| `seam_sum_readout_eq_marker_mul` | Adjacent-pair readouts recover the original edge coefficient |
| `grouped_seam_marked_count_mod_four` | Odd winding on a unit cycle gives residue two |
| `marks_crossing_stack_tile` | A tile with twin vertices inside contributes two marked subtiles |
| `thue_morse_marker_return_control` | Literal proper return-word images preserve the calibrated signed column |

These endpoints are in [PeriodicPartnerReturnBoundary.lean](../proof/PscVerif/PscVerif/PeriodicPartnerReturnBoundary.lean).
The tiling and cohomology instantiations, the fixed-lattice
argument and the geometrical identification of vertex ownership
are written deductions with the stated imports.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

At the Thue–Morse marker `0.0`, use the square `0 ↦ 0110`,
`1 ↦ 1001`. Its second iterates supply all four legal seams and the
nearest negative and positive markers. The four central return
words, in order `010110`, `011010`, `0110`, `01011010`, have
return-substitution images `1320`, `1230`, `120`, `13230` in the
zero-based numbering. The two off-diagonal central words are the
same return word with different positions of the original origin.
The oriented seam cycle gives the fixed column `(1,1,1,−2)`, of
total count one and flattened count zero. Lean checks the literal
images, the marker-free interiors and these count identities.
The period-doubling quotient realizes the odd winding at degree one.

The cubic companion `1/2/10022221` from the
[even stack reduction](c4-even-stack-residue-2026-11-19.md#negative-controls)
also has nilpotent incidence modulo two and a complete original
seam square. The return-cycle calculation applies and retains its
unit cycle. Its explicit strong-coincidence witness excludes it
from the rank-two strict residue. Retention of the return cycle
by itself is therefore compatible with irreducible cubic incidence.

### Non-claims / remaining gaps

The actual boundary term in the hypothetical rank-two geometry
is odd after division by two. A cubic exclusion still needs a
geometric restriction on the twin-vertex readout of the fixed
return vectors, or an independent obstruction to that geometry.
The arithmetic nilpotence and the literal original word obstruction
give no such restriction on their own. The general even-determinant
rank-two case and universal C4 remain open. Independent human review
is pending.
