# The original-word parity constraint for C4 twins

The [return-word proof](c4-return-seam-boundary-2026-11-20.md)
computes the pullback of the stack phase on every original seam cycle.
It implies a parity constraint on aligned balanced words in the
original alphabet. The constraint uses one adjacent marker and two
endpoint groups. It can be replayed without constructing the return
alphabet, stack tiles or twin-vertex lists. The
[literature decision](c4-original-marker-parity-stop-go-2026-11-20.md)
records the inputs.

## Work shown

### Assumptions and hypotheses

Use the standing [even-determinant rank-two residue](c4-even-stack-residue-2026-11-19.md).
Write `q` for the stack projection and `ι` for the deck map. Its
grouped periodic seam graph has four distinct corners and `ι` exchanges
opposite corners. Choose the groups with singleton zero sides, and
write `e₀ = a₀.b₀` for their original seam. The original periodic
seam graph is connected by the eventual-range sequence and the absence
of eigenvalue one on original letter counts.

Use a positive power `τ` of the source substitution such that both
endpoint maps are fixed after one application, all periodic seams are
fixed and the calculation of the odd winding applies. For a word
`τ(a)` let `L(a)` be its last letter and `F(a)` its first letter. On
the original alphabet define the two bits and the internal marker count

```text
ℓ(a) = [L(a) ≠ a₀],      r(a) = [F(a) ≠ b₀],
m(w) = #{ i : 1 ≤ i < |w|, L(w_i) = a₀, F(w_(i+1)) = b₀ }.
```

Consider two original tilings whose stack images are twins. From a
common original vertex to a later common original vertex let their
nonempty words be `u,v` with the same original Parikh vector. Equality
of the two lengths implies this balance on the irreducible cubic
alphabet. Neither vertex needs to be a return marker. The required law is

```text
m(u) − m(v) ≡ 1 + r(first u) + ℓ(last u)   (mod 2).
```

### Derivation / reduction

#### A square root after removing the marker

Let `z` be the odd circle phase on the stack hull. On the original
hull let `H` turn once immediately to the right of each `e₀` cut.
Take a fixed ramp of length `ε` less than the shortest original tile.
On that interval the value is `exp(2πi t/ε)` at distance `t` from the
cut. Everywhere else the value is one. The ramps are disjoint and
their endpoints have value one, so `H` is continuous in the ordinary
tiling topology and has value one at every original vertex. On a
return tile its integral count is one. Its class in the proper
return presentation is the total return count row.

The previous fixed-lattice calculation gives `K W_e₀` for the
readout of `q* [z]` on any original seam cycle `W`, where `K` is odd.
The marker row has readout `W_e₀`. The fixed lattice supplies the
entire eventual return count image modulo two. Consequently
`[z ∘ q]` and `[H]` are equal in degree-one cohomology modulo two.
The coefficient sequence for multiplication by two shows that their
integral difference is twice an integral class. Represent that
class by a circle map. Correct its square by half the real logarithm
of the remaining null class. This gives a continuous map `G` with

```text
G² = (z ∘ q) / H.
```

For any ordered pair `P = (T,T′)` with twin stack images, the ratio
`g_P(t) = G(T−t)/G(T′−t)` satisfies

```text
g_P(t)² = −H(T′−t)/H(T−t).
```

At a common original vertex it is `i` or `−i`. Use bit `s(P)` for
the sign when the vertex is at zero. Interchanging tracks complements
this bit.

#### The endpoint graph forces a common normalized sign

First take opposite periodic seam pairs. For two such ordered pairs
with the same ordered original left rays, the `H` ratios agree for
`t < 0`. The ratio of their `g_P` values squares to one. It tends to
one on the common left tails by uniform continuity of `G` and is
constant on the negative ray. Its value at zero is one. Thus `s(P)`
depends only on the ordered periodic last-letter pair `(a,a′)`.
Call this bit `s_L(a,a′)`.

On the right the first ramp needs a correction. Let `d(P)` be the
marker indicator at the first track's seam minus that at the second
track's seam. For `0 ≤ t ≤ ε`, `g_P(t) exp(πi d(P)t/ε)` has constant
square `−1` and hence is constant. After the ramp the `H` ratios
agree for pairs with the same ordered original right rays. Comparing
on the positive tails gives equal `g_P(ε)` for those pairs. Therefore
`s(P)+d(P)` modulo two depends only on the ordered periodic first
letters `(b,b′)`. Call it `s_R(b,b′)`.

For opposite corners the marker difference is `1 + ℓ(a) + r(b)`
modulo two, since exactly the diagonal pairing includes the singleton
marker. The normalized bits

```text
s_L(a,a′) + ℓ(a),      s_R(b,b′) + r(b) + 1
```

are invariant under interchange of tracks and equal on every pair
of legal opposite seams. Each unordered opposite left pair is indexed
by its member `a ≠ a₀`, and each right pair by `b ≠ b₀`. Their indices
are joined if `a.b` is legal, or if both `a.b₀` and `a₀.b` are legal.
Indeed the former uses the singleton marker as its opposite seam,
and the latter uses the other two corners.

This graph is connected. The neighbours of `b₀` other than `a₀`
and the neighbours of `a₀` other than `b₀` give a complete nonempty
bipartite subgraph. Every other vertex has a path to it in the
original connected seam graph before reaching either removed vertex.
All edges of that path between nonmarker vertices are retained.
The normalized bits are therefore one common bit `c`. This works
for three periodic letters on either side and for incomplete original
graphs that still give the grouped square.

#### Transport along the balanced interval

Inflate the two raw tilings by `τ` repeatedly. At each common cut the
inflated left and right patches tend to the corresponding periodic
raw seam tilings. This follows by nesting the last tile of each
inflated left neighbour and the first tile of each inflated right
neighbour. Deck equivalence is preserved by translation, inflation
and limits. The limiting seams are in opposite groups. The discrete
signs at the two ends are therefore eventually their limiting signs.

On the enlarged balanced interval the real lift of the ratio of the
two `H` phases increments by the difference of the original `e₀`
counts, including the left seam ramp and excluding the right seam.
The equation for `g_P²` transports the sign by that increment modulo
two. Within the interval, markers inside single inflated images
cancel track by track because the words are balanced. A marker
between inflated images is counted by `m` on the original cut,
using the stabilized endpoint maps. At the start, incorporating the
left seam marker replaces `s(P)` by `s_R` on the initial letter pair.
At the finish the sign is `s_L` on the terminal letter pair. Hence

```text
m(u) − m(v) ≡ s_L(last u,last v) − s_R(first u,first v)
            ≡ 1 + r(first u) + ℓ(last u)  (mod 2).
```

The full interval may contain other common vertices. No primitive
bigon or choice of a covering for the original hull is used.

### Evidence and replay

| Lean endpoint | Verified implication |
| --- | --- |
| `normalized_gauges_agree_of_connected` | The opposite-seam equalities make the normalized gauges constant |
| `balanced_marker_difference_of_inflation` | Counts inside whole image words cancel, leaving projected cuts |
| `marker_difference_of_opposite_seams` | The origin marker difference is one plus the two group bits |
| `marker_parity_of_common_gauge` | The common normalized bit cancels |
| `cubic_marker_parity_control` | The two periodic prefixes of `01/112/021` give a literal violation |

These endpoints are in [PeriodicPartnerMarkerParity.lean](../proof/PscVerif/PscVerif/PeriodicPartnerMarkerParity.lean).
The circle map, root transport and application to the stack factor
are written arguments.

For the bounded replay, retain the 96 nilpotent positive-cycle
members of the standing short-image corpus. Test every legal periodic
marker with four populated singleton-group cells. For each marker
compare the periodic right ray at its first letter with the right ray
of an opposite legal seam. Generate the first `σ¹²` words and search
equal-Parikh prefixes. Require opposite projected last letters at the
cut and opposite first letters immediately after it, so the reported
contradiction is the parity condition itself. The search uses the
literal source words with a cap of `3¹² = 531441` letters per ray.
Each recorded witness is a finite exact comparison. A capped search
without a witness would leave that marker unresolved.

| Original seam graph | Specimens | Singleton markers with a violating prefix |
| --- | ---: | ---: |
| Complete two by two | 24 | 96 |
| Two by three with five edges | 6 | 24 |
| Complete two by three | 24 | 144 |
| Three by two with five edges | 6 | 24 |
| Complete three by two | 24 | 144 |
| Complete three by three | 12 | 108 |
| Total | 96 | 540 |

All 540 eligible marker presentations have a witness. The largest
selected prefix has 5,038 letters. These are independent exclusions
of the bounded residue, which already has the strong-coincidence
certificates in the [even-stack note](c4-even-stack-residue-2026-11-19.md#evidence-and-replay).
The independent [Python oracle](../oracles/python/c4_original_marker_parity.py)
replays these results with the original exact incidence screen and a
separate language closure. The canonical regression is
[test_c4_original_marker_parity.mojo](../kernel/tests/test_c4_original_marker_parity.mojo).
Its local execution has no acceptance result. The coverage table is
from the independent replay.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
python3 oracles/python/c4_original_marker_parity.py
(cd kernel && pixi run --locked mojo run -I . -I tests tests/test_c4_original_marker_parity.mojo)
```

### Negative controls

In the degree-one Thue–Morse cover the complementary words `01` and
`10` are balanced. Their internal `00` counts are both zero, their
initial and terminal colours are opposite and the right side of the
law is zero. The Lean control checks these values. The degree-one
odd winding is compatible with the new condition.

For the cubic `01/112/021`, choose marker `1.0` and the opposite seam
`2.1`. The first 30 letters of the two right rays are already present
in the sixth powers. Their Parikh counts agree, the next two letters
are `2` and `1`, and the last two are `0` and `1`, respectively. Both
terminal endpoint group comparisons pass. The internal projected
marker counts are 7 and 8. The first track's initial bit is zero and
its terminal bit is one, so the required parity is even and the
observed parity is odd.

The [equal-run companion calculation](c4-literal-periodic-defect-2026-11-20.md#the-equal-run-boundary)
gives a separate uniform exclusion outside the bounded corpus.
Its level-four coincidence extends the earlier `m<r` witnesses
to `m=r` by using the original words and the existing all-pair
criterion.

### Non-claims / remaining gaps

The written argument gives the necessary law on the entire standing
even-determinant rank-two residue. The replay above covers the
bounded source corpus. The [all-level continuation](c4-marker-reachability-2026-11-20.md)
decides the test on each prescribed pair of periodic seams and gives
a uniform three-letter violation in another family with unbounded
image lengths. Uniform witness existence remains open for the
marker-law approach. The [stack word rigidity proof](c4-nonunit-stack-word-rigidity-2026-11-20.md)
gives a written exclusion of strict systems in the nonunit
three-letter irreducible Pisot class at coincidence rank two.
Independent human review is pending.
