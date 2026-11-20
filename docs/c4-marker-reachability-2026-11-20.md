# All-level reachability for the C4 marker law

The marker test on two specified periodic seams reduces to a finite
path problem at all inflation levels. A three-letter violating
prefix also excludes the even rank-two strict residue for a family
with arbitrarily long images. The [source review](c4-marker-reachability-stop-go-2026-11-20.md)
records the scope of both steps.

## Work shown

### Assumptions and hypotheses

Use the standing [even-determinant rank-two residue](c4-even-stack-residue-2026-11-19.md)
and its [original marker law](c4-original-marker-parity-2026-11-20.md).
Let `M` be the column incidence of the original substitution `σ`.
Write `F,L` for its first and last letter maps. On three letters
`F⁶,L⁶` are idempotent and have the periodic letters as their ranges.
Fix a legal marker `a₀.b₀` and fix two legal periodic seams in opposite
groups. Their right rays start with letters `b,b′` fixed by `F⁶`.
The corresponding left rays end in letters fixed by `L⁶`. In the
rank-two residue the two stack images of these seams are deck twins.
The mod-two reduction of `M³` vanishes.

### Derivation / reduction

#### Correcting the marker at each phase

Let `f₀(x,y)` be the indicator of `L⁶(x)=a₀` and `F⁶(y)=b₀`.
Use six phases, with `f_(j+1)(x,y)=f_j(L(x),F(y))`. This is
consistent modulo six, by the idempotence of `F⁶,L⁶`. Write
`m_j(w)` for the internal `f_j` count in `w` and `A(w)` for
its letter count column. In this section all marker and letter
row arithmetic is in `F₂`. Let `g_j(a)=m_j(σ(a))`. Splitting the
inflated count into within-image and between-image contributions gives

```text
m_j(σ(w)) = m_(j+1)(w) + g_j A(w).
θ_j = g_(j−1) + g_(j−2) M + g_(j−3) M².
C_j(w) = m_j(w) + θ_j A(w).
```

The term `g_(j−3) M³` vanishes, so `g_j + θ_j M = θ_(j+1)`.
It follows that `C_j(σ(w)) = C_(j+1)(w)`. Also `C_j(u)−C_j(v)`
equals `m_j(u)−m_j(v)` whenever `A(u)=A(v)` over the integers.
This is the cancellation that lets the parity register run alongside
the existing [exact Parikh equality automaton](../kernel/psc/coincidence_formula.mojo)
without reading its Parikh state.

#### Recognizing a violating cut

A digit at a letter `a` selects an occurrence in `σ(a)` and
the proper prefix `p` immediately before it. On each track, if
`u` was the full prefix at the previous level, the new prefix is
`σ(u)p`. At depth `k`, store phase `j=−k mod 6`, the current
letter of each track, their previous prefix's last letters (with
absence allowed) and the corrected parity difference. The current
letters determine the proper prefixes. The new last letter is
the last letter of `p` if it exists, and otherwise `L(last u)` if
`u` is nonempty. For the parity, retain the previous difference,
then add the top track's `C_j(p)` and the `f_j` join between
`L(last u)` and `first p`. Subtract the analogous bottom contributions.
An empty side of a join contributes zero. The correction formula makes
this step agree with literal inflation. Both prefixes are initially
empty and the initial parity is zero.

Accept a path only at phase zero with exact equal Parikh vectors
and nonempty prefixes. Compare the projected last letters of
the prefixes and the projected first letters of the current tiles.
A same-group comparison at either side is already a contradiction
for twins. Inflating at that common cut converges to periodic
seams with those projections, and the limiting seams of twins are
opposite. If both group comparisons pass, accept exactly when the
marker parity differs from `1 + [F⁶(b) ≠ b₀] + [L⁶(last u) ≠ a₀]`.
The two image addresses reconstruct the witnessed cut.

At depth `6k` the two proper prefixes and their following letters
are positions in `σ^(6k)(b)` and `σ^(6k)(b′)`. Each position has an
address by tracing its ancestors. The two growing words are nested
along their respective right rays, so every finite cut with its
following letters occurs at one such depth. Equality of lengths
at a common cut is equivalent to exact Parikh equality, by rational
independence of the Perron lengths. This proves both directions of
the recognition claim.

The product uses at most `1728 P + 1` states when `P` is the state
count of the prefix-Parikh automaton. The finite component records
six phases, nine pairs of current letters, four possibilities for
each last letter and two parities, with a shared rejection sink.
If a path is accepted, there is a shortest one without a repeated
state. Breadth-first search can return a literal witness or establish
that the target is unreachable. The proof uses finiteness of the
exact Parikh automaton and applies without choosing a maximum
inflation depth. A resource refusal in its executable construction
still leaves the test unresolved.

There is also a finite certificate for a search with no parity
violation. In the product, forget the accumulated parity and
label each occurrence edge by its parity increment. After ruling
out any reachable same-group target, keep the states reachable
from the root that have a path to a nonempty, balanced,
opposite-endpoint cut at phase zero. On this graph all such cuts
satisfy the law exactly when there is a function `s` to `F₂` with
root value zero, `s(y)=s(x)+d` for every retained occurrence edge
`x→y` of increment `d`, and `s(c)` equal to the required cut value
at every target `c`. An empty retained graph has no target. To prove
necessity, two paths to the same retained state with different totals
would give different parities at a target by following the same suffix.
Thus a state's path sum is unique and supplies `s`. Sufficiency
follows by summing the edge equations along an accepted-cut path.

#### Testing the whole prescribed seam pair

It suffices to test prefixes from the common origin on either side.
Suppose the cuts at `p<q` on the right have opposite groups and
both origin prefixes satisfy the law. The difference of marker
counts on the whole prefix to `q` is the sum of the differences
on the two pieces and the contribution at `p`. If the top last
and first bits at `p` are `ℓ_p,r_p`, that contribution is
`1+ℓ_p+r_p`. Substituting the two prefix laws leaves
`1+r_p+ℓ_q` for the interval from `p` to `q`. Facing left uses
the reversed source words, with first and last maps exchanged and
the reversed marker. Both the internal count and the required
sum of endpoint bits are preserved by this reversal. Concatenating
the two origin intervals gives the law across zero by the same
join identity. Thus both finite tests together decide the marker
and endpoint conditions on all balanced intervals of the specified
two-sided periodic pair.

#### A uniform family with a violation at the third cut

For `t=n+4`, define the following literal substitution, with `n≥0`.

```text
σ(0) = 0210 0^(n+1) 1^(n+3) 2^(n+3) 0
σ(1) = 1201 1^(n+1) 0^(n+4) 2^(n+3) 1
σ(2) = 01   0^(n+3) 1^(n+3) 2^(n+4) 1
```

The first map is `(0,1,0)` and the last map is `(0,1,1)`.
Both are already idempotent. All four seams on `0,1` are legal.
The words for `0,1` contain `00,11` at their fourth cuts,
and the word for `2` begins `010`. Take marker `0.0` and the
opposite seam `1.1`. Both right rays are fixed by `σ`. At the
third cut their prefixes are `021` and `120`. They each contain
one of each letter. The projected last letters are `1,0` and
the projected next letters are `0,1`. The top internal marker
count is one from `0.2`, and the bottom count is zero. The law
requires even parity because the top starts in group zero and
ends in group one. This violates the law for every parameter.
The same witness applies to other word orderings with these first
four letters and endpoint maps whenever the two seams are twins.

The incidence is `M=tJ+E₀₁+E₁₂` with `J` the all-ones matrix.
It is positive, has determinant `t`, and has characteristic
polynomial `P(x)=x³−3tx²−2tx−t`. For even `t`, its reduction is
the strictly upper triangular shift with cube zero. To check the
Pisot condition, evaluate

```text
P(3t)   = −6t²−t < 0,
P(3t+1) = 3t²+3t+1 > 0.
```

There is a root `β` strictly between these endpoints. The cofactor
is `x²+(β−3t)x+t/β`. Its discriminant is negative because
`(β−3t)² < 1 < 4t/β` for `t≥4`. Its two roots are a complex
conjugate pair of modulus `√(t/β)<1`. The positive matrix has
Perron root `β`. This is the only real root, and it is strictly
between consecutive integers. The monic cubic therefore has no
rational root and is irreducible. For each even `t≥4` this gives
a member of the standing arithmetic and seam residue excluded by
the marker law under the even rank-two strict hypotheses. The
maximum image length is `3t+1` and grows with `t`.

### Evidence and replay

| Lean endpoint | Checked implication |
| --- | --- |
| `correction_step`, `corrected_inflation` | The three image rows absorb one inflation's internal marker count |
| `corrected_difference_of_perm`, `advance_register` | A balanced cut reads the original parity and each register update is exact on the two literal prefixes |
| `combine_interval_laws`, `extend_interval_iff` | Testing the two pieces of an interval and the connecting seam is equivalent to the stated concatenation rule |
| `incidence`, `charpoly`, `even_incidence_nilpotent` | The family has the claimed cubic and even nilpotence |
| `endpoints`, `endpoint_maps_idempotent`, `periodic_seams`, `three_letter_violation` | The four periodic seams and the violating cut persist for every parameter |

The endpoints are in [PeriodicPartnerMarkerReachability](../proof/PscVerif/PscVerif/PeriodicPartnerMarkerReachability.lean)
and [PeriodicPartnerMarkerFamily](../proof/PscVerif/PscVerif/PeriodicPartnerMarkerFamily.lean).
The product argument, the reduction from finite words to periodic
rays, and the irreducibility and conjugate bounds are written proofs.

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

### Negative controls

In Thue–Morse the two fixed complementary rays have complementary
blocks. A balanced complementary binary block has even length.
For each adjacent pair the difference of the two `00` indicators
is `1+x+y` modulo two for the top bits `x,y`. Summing leaves the
length minus one plus the first and last bits, so every balanced
complementary block satisfies the law. Lean checks the identity at
arbitrary length in `complementary_words_parity`.

In the family change `0210` to `0120` in the image of `0`.
This preserves the incidence, the endpoint maps and the four
periodic seams. The third cut now compares `012` with `120`.
The endpoint group tests still pass, and both internal counts
are zero. The witness depends on the literal ordering. Lean
checks this cut in `reordered_prefix_control`.

### Non-claims / remaining gaps

This step gives a written finite decision for each prescribed pair
and a uniform family exclusion under the even rank-two strict
hypotheses. Applying the decision to all possible grouped seam
presentations would still require a uniform existence proof for
violating cuts or an independent contradiction on the surviving
presentations. The product is specified through the existing
Parikh automaton and Lean register, with a canonical Mojo product
implementation left open. Independent human review is pending.
