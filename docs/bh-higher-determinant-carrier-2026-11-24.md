# Actual balanced factors and higher determinant BH carriers

**Status.** The implications in Lean are checked locally. The 24 family
members below have exact executable certificates. A proof uniform in
the remaining parameters is open. The [source review](bh-higher-determinant-stop-go-2026-11-24.md)
records the choice of scope and related literature.

## Finite reachability and literal zero hits

Let \(s\) be a ternary substitution with positive lengths \(\ell\) satisfying
\(\ell(s(a))=\beta\ell(a)\), where \(\beta>1\). Fix one ordered balanced word
pair. The ordered reduction of each iterate cuts at the equalities of
the two prefix Parikh vectors. Suppose the physical length of every factor
in every reduction is bounded by \(B\).

Take any two actual marks with a common strict interior, say containing
\([x,y]\) in both interiors with \(x<y\). Choose \(n\) so that
\(\beta^n(y-x)>B\). In the complete ordered reduction, the first factor
whose right endpoint is after \(\beta^n x\) ends before \(\beta^n y\).
Both tracks have the same integral Parikh column at that cut. The next
marks exist because the cut lies strictly inside the original expanded
tiles. A point just to the right of the cut lies in both marks and in
the expanded common interior. Pull back that point through the actual
image partitions. The inverse marks are unique at each strict interior
point, and at depth zero they are the two original selected occurrences.
The resulting full-word path ends at integral displacement zero. The
argument works for every overlap in every seed iterate by starting at
that iterate and applying the same bound.

Finiteness of the actual factor set gives such a bound. It also gives a
finite packet set. Localize each overlap within its common factor
ordinal. Deleting the preceding balanced prefix preserves both types
and the full displacement. The finite union of the marked factor
supports therefore contains the packet set. Every literal
`InteriorStep` from an actual packet is realized in the next whole
iterate by inflating the corresponding two marks at its two digit
positions. This proves closure of the exact seed packet set and includes
all overlaps of the original seed. The forward bounded-gap lemma
consumes this same finite closed carrier contract.

The Lean endpoints in
[`BHBoundedFactors.lean`](../proof/PscVerif/PscVerif/BHBoundedFactors.lean)
record the resulting scopes.

| Endpoint | Consequence |
| --- | --- |
| `whole_zero_hit_of_bound` | A path of literal whole-word marks from the chosen strict overlap to balanced full prefixes |
| `finite_reachable_iff_closed_packet_cover` | For an irreducible seed, finite `ChildNC` reachability iff there is a finite actual-seed cover closed under every literal child with a zero-hit path from each member |
| `terminates_of_closed_diagonal_cover` | If every carrier packet can reach an equal-letter zero, every reachable factor is productive and the balanced-pair algorithm terminates with coincidence |

For the last implication, place the first marks of any actual irreducible
factor back in their positions in the whole iterate. Their preceding
factors give a balanced prefix. An equal-letter zero path from this
packet lifts inside the irreducible factor, where the existing literal
diagonal theorem produces a singleton coincidence.

## Exact finite family members

For \(\sigma_{k,r}=(1,0\,1^k2,0^r1)\), use the positive lengths
\((\beta,\beta^2,\beta+r)\), where \(P(\beta)=\beta^3-k\beta^2-2\beta-r=0\).
Each length scales by \(\beta\) on the literal image. The matrix has
determinant \(r\). The screened field checks primitivity, irreducibility,
and the Pisot property for each instantiated pair. Encode a
bottom-minus-top count difference \((x,y,z)\) as
\[
rz+(x+z)\beta+y\beta^2.
\]
This map is injective since \(r>0\) and \(1,\beta,\beta^2\) are linearly
independent. The verifier checks lattice membership and the decoder
recovers all three coordinates with the opposite sign for Lean's
top-minus-bottom convention.

The carrier starts with the strict overlaps of each of `01/10`,
`02/20`, and `12/21`. It keeps both ordered types and every ordered
image-position pair in each row, including coincidence rows. The scan
advances the position with the earlier right endpoint, and at a tie
advances both. An unvisited pair involving a discarded position would
have at most endpoint contact. The verifier rebuilds the roots and
complete rows, checks every target and ordinal, then checks shortest
ranks to both integral zero and equal-letter zero. A positive rank has
a child of rank one smaller. No edge can decrease the rank by more
than one. These two checks give an actual path and a lower bound on the
length of any path.

For \(4\le r\le11\) and \(k\in\{r,r+1,r+2\}\), the local Mojo replay
certified all 24 carriers. In total it checked 320,376 packets and
1,609,538 ordered child occurrences. All three seeds terminate with
coincidence at each of these parameters by the finite closed diagonal
carrier argument. Reversed seeds follow by swapping tracks and negating
the displacement. The largest shortest depths were 60 to integral zero
and 61 to equal-letter zero, both attained at \((r,k)=(11,11)\). Results
for individual parameter pairs are emitted by the replay. They are
executable instances of the proved contract. The finite graphs have
not been imported into the Lean kernel.

Together with the [existing bivariate result](c4-two-parameter-carrier-2026-11-14.md),
this covers the canonical `01/10` seed for all \(k\ge r\) when
\(4\le r\le11\), and for all \(k\ge r+3\) when \(r\ge4\).
The remaining family bands are \(k=r,r+1,r+2\) for \(r\ge12\).
The upper plus-Class-A chamber and its 70 smaller members have separate
scope. Universal BH, residual A1′, and universal PSC remain open.

## Adversarial controls

- The expanding unit-length Thue–Morse swap has only two reachable
  balanced factors. Lean gives it a closed zero-hit cover and proves
  that neither factor is productive. An integral zero alone cannot
  replace equality of the two selected letters.
- At \((r,k)=(4,6)\), a Cartesian-product scan checks every ordered pair
  of image positions against the interval merge, including diagonal rows.
- The verifier rejects endpoint-only contact, a missing child, a missing
  child of a coincidence, out-of-lattice displacement, the wrong
  ordered digit or target, a false labelled zero, and a forged shortest
  depth. Both resource caps halt without a verdict.

## Replay

Run these commands from the repository root with the pinned toolchains installed.

```sh
(cd proof/PscVerif && lake build PscVerif.BHBoundedFactors)
(cd proof/PscVerif && lake env lean BHBoundedFactorsAudit.lean)
(cd proof/PscVerif && lake env lean BHFiniteReachabilityAudit.lean)
(cd kernel && pixi run --locked mojo run -I . tests/test_bh_two_parameter_carrier.mojo)
python3 tools/make_proof_bank.py --check
python -m pytest -q tests/test_proof_bank.py tests/test_bpa_basics.py \
  tests/test_c4_two_parameter_carrier_oracle.py \
  tests/test_c4_determinant_three_carrier_oracle.py
```

The direct finite search suggests starting a uniform rank proof in the
\(k=r+2\) band. A proposed universal restriction to paths of length
at most 59 already fails at \((11,11)\). The unbounded task is to
prove a parameter-dependent rank or another uniform exit for every
member of a closed actual seed carrier.
