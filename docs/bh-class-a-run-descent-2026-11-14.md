# Class-A selected descent inside the two y runs

## Stop/go

Proceed from the local RUN/RUN entry theorem at
`6ae3ec0fa1d1c87814d27b50283982b07eaf4d07`, based on
[#577](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/577).
Target [#452](https://github.com/larsbx/pisot-substitution-conjecture-research/issues/452)
by seeking a selected, parameter-uniform decrease for `y/y` packets in the
run interior, with two integral coordinates retained. The candidate uses
rounding of the affine update to stay in the run interior as the radius
decreases over two successive actual edges.

- [Akiyama–Lee, §§3–4](https://arxiv.org/pdf/1003.2898) use a graph of
  potential overlaps with child multiplicities, and identify the portion
  connected to coincidences. This supplies the graph context. Their Meyer
  and realization hypotheses do not establish our family-specific entry.
- [Akiyama, §3](https://arxiv.org/pdf/1509.04471) relates overlap coincidence
  to strong coincidences with sufficiently varied control points. A result
  confined to `y/y` packets cannot by itself supply that coverage.
- [Minervino–Thuswaldner, §§8–9](https://aif.centre-mersenne.org/item/10.5802/aif.2884.pdf)
  retain real and finite places for nonunit substitutions. No adelic
  realization or geometric finiteness criterion is assumed here.

The repository's signed x/y strip proof and finite overlap certificates use
other domains. A genuine two-cycle with an exit already refutes strict
decrease along every edge. The selected proof must keep both actual RUN
indices, the full displacement, and the exact strict overlap inequality.
The boundary test is that when the inflated shift exceeds the range of
RUN index differences, nearest-integer rounding can suggest an ordinal
outside the run. The descent may leave a bounded residual strip when the
Pisot contraction approaches one. No source-coverage assertion is planned
without a proof covering these excluded regimes.

## Work shown

### Assumptions and hypotheses

Use the ordered words `x → xy^(n+d)x`, `c → cy^n x`, `y → xy^(n−1)c`,
where `n=k+t+3`, `d=k+2t+5` and `K=k+1`. The normalized exact positive
lengths are `L_y=1`, `L_c=1+h`, `L_x=2+α−h`, with positive inflation `β`.
The only length premise in the family endpoint is the exact scaling
of these literal words. Subtracting the `c` and `y` rows gives `βh=1`.
The `y` and `x` rows give `β=n+2+α` and `βα=d−n+1−2h`. Consequently

\[
\gamma=1-\alpha-2h=K/(\beta+1).
\]

For `k≥4` these equations and positivity imply `0≤α<1` and `n≥7`.
We also use the central-domain lemma separately for any `n≥7` under the
same arithmetic, including smaller `k`.

### Derivation / reduction

Write the full bottom-minus-top offset as `(p,q,b−2p−q)`. The physical
shift is `λ=b+(α−h)p+hq`. Set `R=(n−2)/β` and assume `|λ|≤R` for a
`y/y` parent. For `n≥7` we have `1/2≤R<1`.

A RUN/RUN edge has first two offset coordinates `(b,b−2p)`. Writing
`z` for the child's new second slot, the actual signed gap is

\[
g=(d-n)p+(n+2)b+q-z,
\qquad \lambda' = z-C,
\qquad C=2hp-\alpha b.
\]

The exact length equations give `g=βλ−λ′`. If `|λ′|<1`, the parent
bound implies `|g|<n−1`. Since `g` is an integer, the original ordinals
`1+max(g,0)` and `1+max(−g,0)` are both in `1,…,n−1`. Thus a chosen
integer `z` with the clipping bound is an actual strict child.

Put `M=max(|p|,|b|)`. Round `C` towards zero if the result lies within
`R`. Otherwise use the other adjacent integer. In the latter case the
second distance is below `1−R≤R`, so in both cases

\[
|z-C|\le R,\qquad |z|\le |C|+1-R\le (1-\gamma)M+1-R.
\]

If `γM>1−R`, this gives `|z|<M`. The new slots are `(b,z)`. If `|b|=M`,
the next edge still uses the same strict margin and shrinks the new
slot again. Thus within two edges the integer radius drops. This gives
an actual path to a central packet with `γM≤1−R` by strong induction.
The parent and chosen children retain both original letters and the
entire integer offset. Only the induction measure uses two coordinates.

Multiplying the residual inequality by `β+1` gives
`KM≤(1−R)(β+1)=(4+α)+(1−R)<6`. If `K≥3`, the exact equations also yield
`α<R`, since `β(R−α)=K−3+2h>0`. Then the residual bound is `<5`, so
`KM≤4`. In particular, `K≥5` forces `M=0`. With `p=b=0`, choosing `z=0`
from the central domain gives an actual y/y zero coincidence, with
both literal ordinals obtained from the remaining integer `q`.

**Entry from any pair of parent types.** Let `a_top,a_bottom` be the
parent letters, `R_a` the corresponding literal y-run sizes, and
`F_a` the length of the first letter of `σ(a)`. The signed physical
difference of the two inflated run starts is
`D=βλ+F_bottom−F_top`, now using the starting packet's physical shift
`λ`. If `1−R_bottom≤D≤R_top−1`, round to a nearest integer `g`.
The integer `g` is in the legal gap interval and `|D−g|≤1/2`.
The literal ordinals computed from `g` give a y/y child in the central
strip. Thus for all `k≥4,t≥0`, **every packet satisfying this exact run-gap
condition has a selected strict occurrence path to typed y/y at offset
zero**, regardless of its parent letters. This is the main Lean endpoint.

### Evidence and replay

[ClassARunDescent.lean](../proof/PscVerif/PscVerif/ClassARunDescent.lean)
builds on #577's literal marks and strict geometry. The
[focused audit](../proof/PscVerif/ClassARunDescentAudit.lean) pins the
family endpoint to an independent literal spelling of the three words,
the oriented run sizes, the normalization, and the typed zero packet.
It checks the owned declarations for axioms beyond the standard
`propext`, `Classical.choice`, `Quot.sound` allowlist.

```sh
cd proof/PscVerif
lake build PscVerif.ClassARunDescent
lake env lean ClassARunDescentAudit.lean
```

The focused local check uses Lean 4.34.0-rc2 and prepared transitive
objects. This is a proof-only addition to the existing literal
occurrence infrastructure. The repository's canonical native replays
and hosted exact-head acceptance remain separate gates for #452.

### Negative controls

The alternating `y/y` states with offsets `(1,3,−6)` and `(−1,−3,6)`
admit an actual two-cycle at `(k,t)=(4,0)`. Both radii are one. The cycle
does not block a selected exit, and shows why a decrease along every
edge would give a false theorem. The audit checks both strict edges.

For `p=b=0,q=n`, the physical shift is `n/β<1`, so the parent is strict.
Its inflated run-start difference is `n`. Even the largest legal
RUN/RUN gap leaves displacement at least `2`. The geometric control
rules out calling this a strict RUN/RUN edge. FIRST and LAST fall
outside that control and may provide exits.

### Non-claims / remaining gaps

The proved interval is sufficient for selected escape. This supplies
neither complete source coverage for all cyclic seed-reachable packets
nor a classification of boundary-only components. The remaining
geometry can be isolated exactly. Above `D=R_top−1`, the only possible
strict RUN/RUN choice is the extreme pair `(R_top,1)`, and it is
strict precisely for `D<R_top`. This follows from `|D−(i−j)|<1`
and integer ordinal differences. Below `D=1−R_bottom`, the transposed
statement follows by exchanging the two parents.

For an upper-boundary source define `X=D−R_top` and let `E_top` be the
length of the top image's last tile. If `−1<X<E_top`, select top LAST
and bottom first RUN. These child starts differ by `X` and the two
tiles overlap strictly. If `X≥E_top`, select top LAST and bottom FIRST.
Their starts differ by `X−F_bottom`. This is less than `E_top` by
strictness of the parent and exceeds `−F_bottom` because `X>0`.
The lower-boundary rule is its genuine reversal. This gives actual
boundary choices on paper. Their iteration still needs a progress
argument into the central interval or a separate productive region.

For smaller `k`, finish the bounded residual radius strip and the
cases with `n<7`. Radius alone supplies no enumeration of these packets
across all parameters. The nonunit realization dictionary, general BH,
A1′ and the spectral implication remain separate.
