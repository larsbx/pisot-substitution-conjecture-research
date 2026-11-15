# C4 crossing source separation

**Scope:** [Issue #461](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/461).
Baseline `main@73779d9df90946b678546ff575a3df7ccd08c46b` (merged #465).

## Targeted literature check

[Sirvent–Solomyak](https://web.math.pmf.unizg.hr/~sonja/PDS-final.pdf)
and [Akiyama–Lee](https://arxiv.org/abs/1003.2898) use intersecting tile
interiors in the definition of overlap. A pair of positions with equal
symbolic indices is a separate object. The
[Barge–Diamond good-edge witness](https://www.numdam.org/item/BSMF_2002__130_4_619_0/)
aligns equal letters after equal-Parikh prefixes. It does not provide
an alignment for arbitrary nonzero prefix offsets. The
[hub-prefix crossing lemma](c4-hub-prefix-crossing-2026-11-04.md) finds
an actual nonzero complementary-axis offset at a synchronous symbolic
index. Proceed by testing whether the source occurrences necessarily
overlap before attempting to transport the good-edge witness.

## Integer endpoint certificates

For two prefix endpoints with Parikh difference `g`, the difference
at depth `n) is `M^n g`. If that column is componentwise
nonnegative and nonzero, its Perron length is positive. If the
endpoints are the start of one source and the end of the other,
this certifies strict separation. At that level no descendant of
the first source can align with one of the second, and further
inflations preserve separation. An earlier diagonal would itself
have a nonempty diagonal image at that level, so there is no earlier
witness either. The exact zero vector certifies touching.

Conversely, for primitive irreducible cubic incidence every nonzero
`g` eventually has a strictly signed column `M^n g`. Indeed if
the positive left Perron row `ell` satisfied `ell g=0`, it would
also annihilate `Mg,M²g`, contradicting cyclicity of a nonzero
rational vector for an irreducible cubic. The Perron projection of
`g` is therefore a nonzero multiple of the positive right
eigenvector, and eventually determines the component signs.
Thus for any fixed two words, their complete endpoint ordering
can be certified at a finite level by integer sign comparisons,
with equal endpoint vectors handled as ties. The replay uses only
these integer certificates.

## Uniform physical crossing

Keep the hypotheses of the [strict flat crossing lemma](c4-hub-prefix-crossing-2026-11-04.md),
including one common sign on all actual ordered children.
Use the positive Perron row `ell` as the letter lengths and lay
the two words of each hub-oriented pair over the same interval.
Let `H(t)` be the number of completed top hub occurrences minus
the number of completed bottom hub occurrences at position `t`.
For any common positive length vector `w`, integration over the
piecewise constant count difference is the exact weighted sum
```text
A_w(u,v) = Σ_x w_x K_hx(u,v).
```
On a letter of type `x`, each preceding hub contributes length
`w_x`. The previously proved cancellation `Dz=0` for the
positive Perron vector of the child-incidence matrix makes the
weighted sum of these areas zero for every `w).

Choose a state with `A_ell <= 0`. The top hub completes before
the first bottom hub because only the top word begins with the
hub. So `H>0` on an interval of positive length, and the area
bound forces a negative interval too. The first negative jump
occurs at the right endpoint of a bottom hub occurrence with no
simultaneous top hub completion. Let that bottom hub be
`v[j]`. On its entire open interior the completed counts on
both tracks agree. Indeed, the bottom completed count is constant,
the top count is nondecreasing, and just before the first
negative jump the two counts must be equal.

The top letter `u[i]` active immediately after the start of
`v[j]` is a nonhub. If it were a hub, its equal width and
earlier or equal start would make it complete within the
bottom interval or at the negative jump, both impossible.
The two preceding prefixes thus have equal hub count.
Write `E=p(u[:i])-p(v[:j])`. This vector is nonzero: equality
would force `i=j`, and the resulting internal balanced cut
would contradict irreducibility of the pair. At the initial
cut, the bottom word does not start with the hub.
The nonzero defect cannot have zero Perron length by cyclicity.
Therefore the actual source positions satisfy
```text
u[i] != h,  v[j] = h,  E_h = 0,  -ell[u[i]] < ell E < 0.
```
In words, the bottom hub begins strictly inside the top nonhub
occurrence. This yields a genuine overlap, with an integer
endpoint certificate as above. The indices `i,j` need not
agree. In general `E_h=0` only gives the complementary plane,
since the sum of the defect coordinates is `i-j`.

## Exact separation and overlap in the controls

For `1/02/220`, take the fourth ordinal-zero child of the
swap `(01,10)`, then orient it with hub 1 on top:
`(12202202201,02220220112)`. Both words occur in
`sigma^6(2)`, at positions 32 and 153. The genuine good
edge is `{0,2}`, with the earlier depth-four witness.
The unit-length crossing uses indices `(9,9)`, letters
`(0,1)`, and `E=(-1,0,1)`. The gap from the bottom source's
end to the top source's start is certified by
```text
E-e_1=(-1,-1,1),    M(E-e_1)=(0,-1,1),    M²(E-e_1)=(0,0,1).
```
These source occurrences cannot produce a diagonal with one
another at any depth. The pair itself is productive, and its
one-step row already leaves the hub condition on the last
child `(02,20)`. This refutes a local transfer from a symbolic
crossing and a genuine good edge to address-level productivity.

For this same pair, the depth-two integer lengths `(2,4,7)`
certify the full endpoint ordering. The first negative
weighted jump uses indices `(8,9)`, letters `(2,1)`, and
`E=(-1,0,0)`. The top interval is `[43,50]` and the bottom
interval is `[45,49]`. Exhausting all actual top nonhub/bottom
hub overlaps with `E_h=0` gives only this pair, so no such
physical overlap in this state lies on the symbolic axis.
The corrected source occurrences are productive: their
three-step addresses `[1,0,0]` and `[1,0,1]` meet at cut 104
with a common `2` and prefix Parikh vector `(32,14,58)`.

For the productive phase-zero control `01/12/021`, the pair
`(1201,0112)` has the same first weighted overlap type
`(2,1,-e_0)`, now at indices `(1,2)`. Depth-two integer
lengths `(4,5,7)` certify its full endpoint ordering.
Its first weighted overlap yields a `1/1` diagonal at cut 27,
with digit paths `[2,1,2]` and `[1,0,1]`. Its separate
synchronous crossing yields the previously verified `0/0`
at cut 28. The reducible strict control with genuine good edge
remains a calibration for why Pisot cancellation is needed.

## Replay and remaining implication

```sh
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_recurrent_flat_exits.mojo)
python -m pytest -q tests/test_c4_recurrent_flat_exits_oracle.py \
  tests/test_c4_complete_cone_hub_audit_oracle.py \
  tests/test_c4_two_generation_rank_oracle.py
```

The uniform physical crossing is proved above. The native
and independent oracle checks certify the fixed words,
integer endpoint orders, offsets, and literal descendant
addresses in the controls. Productivity of every forced
physical overlap and the required one-step Sync newborn
remain open. No governed claim changes.
