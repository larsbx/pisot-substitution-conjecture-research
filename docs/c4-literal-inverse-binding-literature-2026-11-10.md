# C4 literal inverse-row binding: literature stop/go

Date: 2026-11-10. Recorded before new implementation. Sources: accepted
`main@8c04ec85e12d9370481a493bb2c8f822cbb81a2d` and the historical finite
overlap branch at `0f4b9a05ce95e59d9b6cde11fcdf22d161375030` (PR #497).
The append-only side ledger and the #537 handoff were inspected first.

## Proposed claim and decision

**Proceed with finite literal source binding and an explicit orientation
adapter.** Reconstruct every old inverse row slot as a pair of actual
positions in the words of `sigma^2`. Retain the source letters, selected
letters, prefix counts, exact integral inverse equation, and the bit that
records whether the resulting ancestor was swapped into its canonical
representative. Prove the finite ancestry/orientation interface and audit
internal occurrence completeness on the supplied finite domain.

The executable target is the existing twelve-source class
`11/{012,021,102,120,201,210}/{01,10}`. Its two-step incidence has determinant
four. The old rows count repeated targets but do not serialize their marks;
their deterministic constructor provides the data needed to recover them.
No compact nonemptiness or positivity conclusion follows from that recovery.

## Primary sources inspected

| Primary text and locator | What transfers | Hypothesis boundary |
| --- | --- | --- |
| Akiyama--Lee, *Algorithm for determining pure pointedness of self-affine tilings*, [arXiv:1003.2898v1](https://arxiv.org/html/1003.2898v1), Section 4, equations (4.1) and (4.4), Theorem 4.1 | The pair-intersection decomposition indexes pieces by both actual digits. Equal targets need not be the same occurrence. | Their spectral criterion assumes a self-affine tiling and Meyer return set. An authenticated finite packet graph supplies neither. Empty, boundary-only and positive overlaps remain distinct. |
| Barge--Diamond, *Coincidence for substitutions of Pisot type*, [BSMF 130 (2002), pp. 621--623](https://www.numdam.org/item/10.24033/bsmf.2433.pdf) | Literal image prefixes and the incidence action define the translated segments. This fixes the integral affine sign and the meaning of each selected position. | The configuration argument concerns actual strands. A normalized packet, a finite cycle, or a projected offset is not a common legal strand. |
| Minervino--Thuswaldner, *The Geometry of Non-unit Pisot Substitutions*, [arXiv:1402.2002](https://arxiv.org/pdf/1402.2002), Lemma 3.1 and Theorem 8.3 | The full representation space supports prefix-indexed compact set equations and product-Haar scaling. Track exchange changes overlap sets by translation. | Finite places cannot be discarded in the nonunit case. Compact cover, lattice-range compatibility, measure-disjointness and a positive strict-cut root require their own arguments. |

These texts were opened for this gate. The overlap decomposition and affine
coordinate changes are standard. The contribution sought here is an exact
source binding for this repository's archived finite graph and accepted
Lean occurrence interface, not a new general overlap theorem.

## Exact proposed finite contract

For canonical inverse source `p=(a,b,z)` and actual marks
`sigma^2(A)=P a S`, `sigma^2(B)=Q b T`, solve only the integral equation
`M^2 y=z+pi(Q)-pi(P)`. Its raw target is `u=(A,B,y)`.
A row record must distinguish `u` from `swap(u)` even when both normalize
to the same stored target. A quotient target number alone is insufficient.

On the ordered lift of the supplied canonical state set, retain exactly
the position pairs whose integral ancestor belongs to that lift. An audit
must check equality of these occurrence inventories, not just equal row
lengths or adjacency multiplicities. Roots are the distinct-letter,
zero-offset pairs and their swaps. A discovery witness from an earlier
state, with its orientation bit, can inductively certify inverse ancestry.
The theorem `ancestry_packet_transpose` then has explicit finite premises;
it must not silently stand in for a Lean check of every serialized source.

For later geometry, if `E(p)=K_a intersect (K_b+star(z))`, then
`E(swap(p))=E(p)-star(z)`. The raw incoming piece is
`A(E(u))+star(pi(P))`. When the stored target is `swap(u)`, its translation
is instead `star(z+pi(Q))`. Retaining this distinction now prevents the
count-only quotient from corrupting a later compact-cover construction.

## Negative controls and remaining obligations

Reject a missing or duplicated position pair, swapped unequal positions,
a forged prefix or selected letter, reversed signs, an erased
normalization bit, a rounded nonintegral preimage, a target outside the
represented domain, and an invalid or circular discovery witness. A
repeated target is a required calibration, not permission to deduplicate.

The earlier inverse-closed/forward-leaking control remains valid. A finite
internal edge certificate need not prove inverse closure of all compact
pieces, justify stable-box pruning geometrically, or prove positive compact
overlap from positive interval length. Preserve all historical archives and
their source pins. C4, Concentration, global G1 and PSC remain open.
