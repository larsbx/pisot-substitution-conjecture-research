# Strict RUN/RUN entry into the minus-Class-A zero-defect slice

## Stop/go

Proceed with the first edge of the RUN/RUN construction at
[#577, `01c4e376a652fd93e981e7b302e989c65774a0de`](https://github.com/larsbx/pisot-substitution-conjecture-research/tree/01c4e376a652fd93e981e7b302e989c65774a0de).
The question is whether the geometric condition for that edge is weaker
than the ordinal guard for taking the subsequent direct zero-return edge.
The targeted review in the [Class-A entry stop/go record](bh-class-a-entry-stop-go-2026-11-14.md)
identifies the prior overlap-graph and literal-prefix framework in Akiyama–Lee,
Akiyama, and Minervino–Thuswaldner. This follow-up reuses the same actual
occurrence relation and imports no spectral implication. The checked
negative control is the `y/y` endpoint overrun from #577. Its exit
requires four edges at `n=3`, and the subsequent direct edge cannot
serve as a hypothesis for entering that source. Test the exact signed
strict-overlap cutoff, including equality, and retain the actual two
source ordinals.

## Work shown

### Assumptions and hypotheses

Use the literal minus-Class-A images `x → xy^(n+d)x`, `c → cy^n x`,
`y → xy^(n−1)c`, with `n ≥ 2`, positive lengths `ℓ`, and positive exact
substitution scaling `β`. Write source offsets bottom minus top in
`(x,c,y)` order. The parameterized family has `n=k+t+3` and `d=k+2t+5`.
The Lean clipping theorem takes the exact length equations as inputs.

### Derivation / reduction

For source `(a,b,p,q,r)` write `S=p+q+r` and let `δ` be the difference
of the indicators that the first letters of the two images equal `x`.
Set `h=q+(d+1)δ−(d−n)S` and `R=(n+d,n,n−1)`. A RUN/RUN child has both
letters `y`. Its first offset is `p+S−δ`, so a child in the zero-defect
slice requires `p+S=δ`. Under that equation the second offset is `2S`,
and for actual ordinals `i,j` the third offset is `h−2S+j−i`. Thus the
required gap is exactly `i−j=h`. It can be attained precisely when
`1−R_b≤h≤R_a−1`, by `i=1+max(h,0)`, `j=1+max(−h,0)`.

The resulting child is `(y,y,0,2S,−2S)`. Subtracting the exact length
equations for `c` and `y` gives `β(ℓ_c−ℓ_y)=ℓ_y`. The child tiles both
have length `ℓ_y`, so strict overlap holds precisely when `|2S|<β`.
The actual child and its strictness imply the source interior by
[#577's backward containment theorem](../proof/PscVerif/PscVerif/ClassAZeroDefectEscape.lean).
In the minus-Class-A chamber `n+2<β<n+3` follows from the documented
`β=n+2+ρ+h_len` and `ρ+3h_len<1`, where `h_len=1/β`. Consequently
`|2S|≤n+2` is the integer form of the exact clip. The prior sufficient
condition `|2S|≤n−1` controls a second direct zero-return edge.

Combining the exact first edge with #577's written ten-edge slice
theorem bounds these sources by eleven edges to integral zero. Lean
also directly checks the special case `2S=n+1`: the first literal edge
composes with #577's checked four-edge overrun path to `y/y` at zero
integral offset. This takes five edges. Its analogue under exchanging
top and bottom follows on paper by swapping the literal address pairs.

### Evidence and replay

The [Lean source](../proof/PscVerif/PscVerif/ClassAZeroDefectEscape.lean)
proves the selected first edge with the exact geometric cutoff and
composes the five-edge path. The
[focused audit](../proof/PscVerif/ClassAZeroDefectEscapeAudit.lean)
retains literal words, addresses and path endpoints in independently
stated types. Replay from the candidate source with pinned dependencies:

```sh
cd proof/PscVerif
lake build PscVerif.ClassAZeroDefectEscape
lake env lean ClassAZeroDefectEscapeAudit.lean
```

The local check uses Lean 4.34.0-rc2 and prepared transitive objects.
The audit checks all declarations owned by the module and all seven
endpoint types, and rejects missing, wrong-type and extra-premise
controls. The broader written slice theorem is an input to the
11-edge claim above. The five-edge path is checked directly in Lean.

### Negative controls

At equality with the geometric cutoff the two open child interiors
have no intersection. The audit checks refusal at that boundary. At
`n=3`, `d=5`, `(x,x,−2,4,0)` takes actual ordinals `(1,1)` to the
`y/y` overrun with `2S=4>n−1`. The path is still certified under positive
exact length scaling, using the inherited four-edge suffix. This shows
the old sufficient guard cannot characterize the first strict edge.

### Non-claims / remaining gaps

The result handles entry through RUN/RUN with an explicit source
condition. Issue [#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452)
still requires an actual path from every required cyclic seed-reachable
source into this preimage or another established productive region.
The proof supplies no coverage of those cyclic sources, no extension to
arbitrary substitutions, and no spectral implication.
