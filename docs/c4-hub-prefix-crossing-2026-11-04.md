# C4 hub-prefix crossing from flat orientation

**Target:** [Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@3b29bf03c87743b56ff1095288a29c3ae78b17a1` (merged #464).

## Targeted literature check

[Barge–Diamond](https://doi.org/10.24033/bsmf.2433) supplies the eventual
prefix-coincidence witness at zero prefix defect for a good pair.
[Sirvent–Solomyak](https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf)
separates literal irreducible balanced factorization from eventual
coincidence. [Reutenauer](https://doi.org/10.1093/oso/9781383025965.003.0007)
gives the general scattered-subword and Magnus algebra background.
The repository's [wedge route](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/85)
already uses the signed degree-two intertwiner and the rational wedge-span
dichotomy. The [good-edge bridge](c4-good-edge-system-bridge.md) fixes the
hub gauge and shows that viable first-child phases agree. This note tests
a new consequence of uniform flatness. It uses the actual signed area
of hub-prefix discrepancies to extract an occurrence on the good-edge
axis. Neither existence of a closed Pisot component nor productivity of
nonzero offsets transfers from the cited results.

## Uniform crossing lemma

Let `sigma` be a primitive irreducible ternary Pisot substitution, with
incidence matrix `M` and Perron eigenvalue `beta`. Let `C` be a supplied
finite nonempty strongly connected strict child-closed system of
irreducible balanced pairs. Fix a hub letter `h` occurring on exactly
one side at the start of every pair. Orient each pair so that this hub
is on top. Assume every actual child in every complete ordered row has
the same sign `s` relative to that orientation, where `s=+1` preserves
the physical sides and `s=-1` exchanges them.

Then some state `(u,v)` has an internal prefix `i` with
`p(u[:i])_h < p(v[:i])_h`. More precisely there is an actual position
`j` with
```text
E = p(u[:j]) - p(v[:j]) = k(e_a - e_b),   k != 0,
u[j] is in {a,b}, v[j] = h,
```
where `{a,b}` is the complementary pair. If that pair is the
witnessed good edge, this is a nonzero defect on the good-edge axis.

**Proof.** Let `N` count all ordered children with multiplicity, and
write `P` for the common Parikh columns. For each oriented state define
`D` to have column
`d=(K_01,K_02,K_12)`, where `K_xy` is the top-minus-bottom
difference in counts of scattered subwords `xy`.
Balance gives `K_xy=-K_yx` and `K_xx=0`.

Concatenating balanced factors adds their `d)'s, since cross-factor
counts depend only on the common Parikh vectors and cancel.
Substitution sends `d` to `W d`, with `W=Λ²M` in the ordered wedge
basis. To see this, same-source-letter contributions cancel by
balance, and contributions from two different positions transform
the antisymmetric count matrix by `K -> M K M^T`.
The actual full child row therefore gives
```text
P N = M P,             s D N = W D.
```
The sign is common across all children by assumption. Take the
positive Perron right vector `z` of `N`. Then `Pz>0` since the
nonzero image `Pz` is a nonnegative eigenvector of primitive `M`.
Thus the Perron eigenvalue of `N` is `beta`.
Every eigenvalue of `W` has modulus strictly smaller than `beta`:
they are products of distinct incidence eigenvalues, and the two
non-Perron roots have modulus below one. So `W Dz=s beta Dz`
forces `Dz=0`.

The hub area is a linear functional of `d`:
```text
A_h(u,v) = Σ_{i=0}^{|u|-1} [p(u[:i])_h - p(v[:i])_h]
         = Σ_{x != h} K_hx(u,v).
```
Indeed each occurrence of the hub contributes once for every letter
strictly to its right, with the equal hub/hub counts cancelling.
The positive `z`-weighted sum of the areas vanishes. Every state
starts with hub discrepancy `+1`, so a state with no negative
hub prefix has area at least one. At least one state has area
nonpositive and hence a negative prefix. Let `j+1` be the first
such prefix. Unit steps give `E_h=0` at `j`, with top letter
different from the hub and bottom letter equal to it. The full
defect cannot vanish at this internal position by irreducibility.
Its three entries sum to zero, giving the stated axis. ∎

In fact every root has a positive asymptotic lower fraction of
crossing factors in its complete inflations. If `B` bounds the
absolute area of every oriented state, each noncrossing factor has
area at least one and each crossing factor has area at least
`-B`. At depth `n`, all factors have the same physical sign
`s^n` relative to their hub orientations. If `r_n` counts all
factors and `c_n` counts crossings, then
`r_n-(B+1)c_n <= |A_h(sigma^n(u),sigma^n(v))|`.
The right side grows at a rate strictly below `beta`, by the
exterior-square spectrum. The left count `r_n` grows at least as
a positive constant times `beta^n), since factor lengths are
bounded and the primitive substituted root has that length growth.
Thus `liminf c_n/r_n >= 1/(B+1)`. These are algebraic arguments
using the Pisot hypotheses. The executable checks use integers only.

## Exact controls and the offset interface

| Substitution | Hub | Actual hub-oriented areas | Scope |
| --- | --- | --- | --- |
| `10/102/211` | 2 | `2,4,2,2` on the four strict states | All hub-prefix discrepancies are nonnegative. The good edge `{0,1}` is genuinely prefix-coincident at depth one. The phase is zero. The non-Pisot incidence eigenvalue 1 allows the exterior-square eigenvalue `beta`. |
| `1/02/220` | 1 | `8` on the recurrent state, `8,5,5` on its hub-oriented child row | No hub crossing occurs in that row. The phase is one and the two exits carry the area that the recurrent restriction omits. |
| `01/12/021` | 1 | `1; 0; -3,1` on the complete depth-zero through depth-two cone | The phase-zero cone contains crossings and is productive. |

For the last control, the level-one pair `(1201,0112)` crosses from zero
to minus one in the hub coordinate at source index 2, with oriented
letters `(0,1)` and `E=(-1,0,1)`. The complementary good edge is
`{0,2}`. This source occurrence is independently productive:
`M³ E=(2,3,2)`, and in `sigma³(0)` and `sigma³(1)` the common
letter `0` at respective positions 0 and 7 has bottom-minus-top
prefix mass `(2,3,2)`. Its digit paths are `[0,0,0]` and
`[1,1,0]`. In the full level-one pair's threefold inflation the
two addresses meet at absolute cut 28, where the common prefix
mass is `(7,12,9)`. The next cut, 29, closes the literal
diagonal factor. This recovers a known global diagonal through
the particular crossing source address.

The general axis condition is weaker than the cancellation in this
fixture. The good-edge witness aligns its two letters at *zero*
defect. Simply reusing such a witness at a nonzero defect leaves a
nonzero transformed defect under invertible incidence. Also, the
crossing source letters have the hub on the bottom, so their pair
differs from the complementary good edge. A further argument must
derive offset cancellation or a one-step synchronizing newborn
from the actual ordered crossings. Neither is asserted uniformly.

## Replay

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_recurrent_flat_exits.mojo)
python -m pytest -q tests/test_c4_recurrent_flat_exits_oracle.py \
  tests/test_c4_complete_cone_hub_audit_oracle.py \
  tests/test_c4_two_generation_rank_oracle.py
```

The replay checks the fixed words, areas, literal source and child
positions, and the diagonal witness. The uniform crossing and
density statements have the mathematical derivations above.
C4, G1 and PSC remain open at this scope.
