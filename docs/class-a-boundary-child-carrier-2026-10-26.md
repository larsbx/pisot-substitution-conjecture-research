# Class-A boundary rays: complete children of the aligned seed

Status: scoped symbolic one-step classification, not a forward-closed carrier
or boundary-hitting theorem. Independent human review pending.

## Targeted stop/go

The proposed increment completes the nine first/run/last pair types from
`(x,c,0)` and adds occurrence/Parikh/geometry/target verification usable for
other parents. Read before implementation: the append-only side-notes ledger,
the [existing stop/go](class-a-gap-uniformity-stopgo-2026-10-23.md), and
the [current chamber proof](class-a-boundary-chamber-2026-10-26.md).

Primary-source check, 2026-10-26:

* Akiyama--Lee, [Algorithm for determining pure pointedness of self-affine
  tilings](https://arxiv.org/html/1003.2898v1), sections 2.5, 3 and 4:
  actual interior overlap and potential overlap are different; the
  Meyer/realized-tiling hypotheses of the global algorithm are retained.
* Barge--Stimac--Williams, [Pure discrete spectrum in substitution tiling
  spaces](https://arxiv.org/html/1107.3598v1), introduction and section 3:
  balanced-pair/overlap procedures are prior art, and a criterion still needs
  its termination/coincidence hypotheses. No new spectral transfer is used.
* Minervino--Thuswaldner, [The geometry of non-unit Pisot
  substitutions](https://www.numdam.org/item/AIF_2014__64_4_1373_0/):
  non-unit representation includes non-Archimedean factors. Physical overlap
  in this note does not remove the separate realization/internal-space debt.

Decision: proceed with the narrowed exact one-step specialization. The
standard affine overlap update is not a novelty claim. Counter-controls are
same-index disjoint y/y pairs, illegal occurrences, endpoint-only contacts,
and altered target types/Parikh coordinates. A self-loop cannot refute an
existential descent unless every alternative is also excluded.

## Work shown

### Assumptions and hypotheses

Use exactly the `eps,k,t,n,d` boundary chambers of PR #347, with `k,t>=0`.
Letters `(x,c,y)` have coordinates `(0,1,2)`; offsets are bottom minus top.
Let `r=floor(u)`, where `u=d/(beta-1)` is strictly between `r` and `r+1`.
The certified chambers give `r=1` for minus; plus gives `r=2` at `k<=3`
and `r=1` at `k>=4`. No decimal eigenvalues enter any decision.

### Derivation / reduction

Normalize by `L_y>0`, writing `a=L_x/L_y`, `b=L_c/L_y`.
Subtracting the actual Perron image-length equations yields

`a-b=u`, `b=1-eps/beta`.

In particular **minus has `1<b<2`, plus has `0<b<1`**. This distinction
changes the final run/last index; the minus upper bound must not be copied
to plus. The top image is `x y^(n+d) x`, the bottom `c y^n x`.
Their first/run/last starts are `(0,a+i-1,a+n+d)` and `(0,b+j-1,b+n)`.
Strict child overlap is `-length_bottom < shift < length_top`.

| Top/bottom occurrence | Exact admissible indices | Child and full Parikh offset |
| --- | --- | --- |
| first/first | `i=j=0` | `(x,c,0,0,0)` |
| first/run | `i=0`, `1<=j<=r+1` | `(x,y,0,1,j-1)` |
| first/last | none (`n>u`) | excluded |
| run/first | none (`a>b`) | excluded |
| run/run | `1<=i<=n+d`, `1<=j<=n`, `j-i in {r,r+1}` | `(y,y,-1,1,j-i)` |
| run/last | `j=n+1`, `n-r<=i<=n+2` minus, `n-r<=i<=n+1` plus | `(y,x,-1,1,n-i+1)` |
| last/first | none | excluded |
| last/run | none | excluded |
| last/last | none (`d>b`) | excluded |

For first/run, the sole nontrivial inequality is `j<1+u`.
For run/run it is `abs(j-i-u)<1`, already certified in PR #347.
For run/last put `v=n-i+1`. Its shift is `v-u`; the two strict
inequalities reduce to `i>n-u` and `i<n+1+b`. Integer rounding gives
the table. Last/run is disjoint because its top start exceeds the end
of every bottom run; last/last would require `d<b`, contradicted by `d>=5`.
The cone certificates give `n>=3` minus, `n>=4` plus, `d>=5`, and all
listed indices lie in their actual words. These prove the table for all
unbounded chamber parameters, separately from finite replay.

There are exactly `2n+4` ordered child occurrences minus and `2n+3` plus.
After retaining multiplicities until projection, the distinct target labels
number `2r+7` minus and `2r+6` plus (9, 10, 8 in the three chambers).
Run/run multiplicity is `2n-2r-1`; all other rows have unique labels.
This is a complete outgoing star of one parent, **not** a forward-closed graph.

### Evidence and replay

Canonical `kernel/psc/class_a_boundary_children.mojo` binds exact symbolic
prefix endpoints to the table and provides the arbitrary-parent
`verify_member_edge` guard. `kernel/tests/test_class_a_boundary_children.mojo`
enumerates every ordered seed child pair in 12 fixed members, and every
child of both `T_m` labels in three chamber representatives. Driver:
`kernel/class_a_boundary_children.mojo`.

`oracles/python/class_a_boundary_children.py` is independently written with
literal word prefixes and integer polynomial coordinates; signs use rational
Perron enclosures with an explicit 512-refinement refusal budget. Its archived
receipt covers **56 members and 23,828 ordered seed pairs**, including all
`k=0..6`, `t=0..3`, both signs. It records 8, 14, 30 actual `T_m` child
occurrences escaping the one-step star at `(-1,0,0)`, `(1,0,0)`, `(1,4,0)`.
These finite counts do not establish uniform closure or rank.

Replay from root:
```sh
python -m pytest -q tests/test_class_a_boundary_children.py tests/test_class_a_boundary_chamber.py
python oracles/python/class_a_boundary_children.py
```
From `kernel/`:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_children.mojo
pixi run --locked mojo run -I . class_a_boundary_children.mojo
```
From `proof/PscVerif/`: `lake build`. `PscVerif.BoundaryRounding` proves
the three integer-rounding equivalences over rational open chambers; it
assumes the bounds and does not formally prove the Perron root statements.
Dedicated native/Python CI: `.github/workflows/class-a-boundary-children.yml`;
the repository Lean gate imports the new module through `PscVerif.lean`.
Local Python replay: nine tests passed. Native and Lean acceptance require
fresh hosted receipts and are not inferred from local Python success.

### Negative controls

Retain all five excluded type pairs, same-index run/run disjointness, invalid
ordinals, mutated target coordinates/types, and the plus run/last index
`i=n+2` that is geometrically valid only on minus. Fail closed on bad
parameters, unavailable occurrences, undecided signs or exhausted budgets.

### Non-claims / remaining gaps

No forward closure, uniform rank, obstruction contradiction, target-aware
interior boundary hit, universal BH, A1-prime, G1 or PSC. A target label in
this star is not an asserted successful boundary packet.

The smallest next symbolic family is already explicit:
`T_m=(y,y,-1,1,m)`, `m in {r,r+1}`, with shift `(m-u)L_y`.
Its run/run descendants have normalized shift
`m*beta-d-u+(j-i)`, with `1<=i,j<=n+eps`.
Every child has Parikh c-coordinate `m+1` (all proper prefixes of sigma(y)
have c-coordinate zero), so none has zero Parikh offset in one step.
This also refutes using the c-coordinate itself as a strictly decreasing
nonnegative rank: it rises from 1 to `m+1` on every actual successor. It does
not exclude another rank or later hits. All actual successors leave the
one-step star, whose c-coordinates are only 0 or 1; thus this proposed finite
label packet is demonstrably not forward closed, uniformly in the chamber.

For the next symbolic rounding obligation put `N=n+eps`,
`B=m*beta-d-u`, `a=b+u`. Every first/run/last combination is covered by
the following strict guards, always intersected with real word bounds:

| Top / bottom kind | Necessary and sufficient guard on B |
| --- | --- |
| first/first | `-a < B < a` |
| first/run j | `-a-j < B < 1-j` |
| first/last | `-a-b-N < B < -N` |
| run i/first | `i-1 < B < a+i` |
| run i/run j | `-1 < B+j-i < 1` |
| run i/last | `i-1-N-b < B < i-N` |
| last/first | `N < B < a+b+N` |
| last/run j | `N-j < B < N-j+1+b` |
| last/last | `-b < B < b` |

The full target is always
`(child_top,child_bottom,(m-1,m+1,m*(n+eps)-d)+prefix_b-prefix_t)`.
The generic member verifier handles each of these without assuming packet
membership or discarding first/last children. The next unfinished symbolic
case is resolving these floor/ceiling guards for `T_r`, then `T_(r+1)`,
on all `k,t`, retaining the resulting new labels in a closed carrier. No
strict uniform spectral margin or accepted well-founded rank is supplied.
