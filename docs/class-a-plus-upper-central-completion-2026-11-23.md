# Upper plus-Class-A: literal central and all-source Lean completion

Date: November 23, 2026. Local continuation of the
[literal entry formalization](class-a-plus-upper-literal-entry-2026-11-23.md)
at local review head `5b8bd353f1934e67b8fbac518a9737eb7abf127d`.
The published source baseline remains merge
`7bfcd8c15e845f148b3c0ee405ca839ae6039e2d`, whose tree equals accepted source
head `1bdaa34c63e6de97a0f17998c4f06887a18f099c`.
This increment is a local, unpublished proposal; its acceptance record is
the separately retained [evidence packet](../evidence/class-a-plus-upper-central-completion-2026-11-23/README.md).

## Result and scope

The new Lean assembly completes the previously separate central-source
obligation and concatenates it with literal entry. For every integer
`n>=7`, `n+5<=d<=2n+11`, it proves existence of a bracketed cubic root,
positive literal eigenlengths, and a finite original-occurrence path from
**every strict integral typed source** to typed `y/y` zero. The endpoint
retains both original `MarkTrace` witnesses, all three offset coordinates,
and separate source-dependent entry and central length bounds.

The strongest endpoint is
`Psc.ClassAPlusUpperCentralCompletion.exists_root_all_source_completion`.
Its only outer premises are the three parameter inequalities. Its
universal source clause requires the actual source's strict overlap for
the constructed length row. Root existence, positive scaling, half-tie
exclusion, the literal central trajectory, recurrence classification,
finite pair bound, terminal height range, and productive cycle exit are
all proved dependencies, not additional hypotheses supplied by a caller.

This is the complete occurrence-path theorem in the stated upper chamber.
It does not promote universal BH, residual A1-prime, general C4, or a new
spectral theorem. The 70 smaller upper members retain their separate
complete swap-seed certificate scope. Independent human review and hosted
acceptance of this local candidate are not claimed.

## Work shown

### Assumptions and hypotheses

Retain `(x,c,y)=(0,1,2)` and the literal words

```text
sigma(x) = x y^(n+d) x,
sigma(c) = c y^n x,
sigma(y) = x y^(n+1) c.
```

Put `J=2n+12-d`, so `1<=J<=n+7`. The root and normalized lengths satisfy

```text
n+4 < beta < n+6,
beta^3-(n+4)beta^2+(n+5-d)beta-2 = 0,
Lx = beta-n-2+1/beta,  Lc = 1-1/beta,  Ly = 1.
```

The existing root-existence and literal-scaling lemmas provide the row
and prove `physicalLength(sigma(a))=beta*La` for every letter. This
endpoint does not silently substitute a different word, companion
matrix, or unspecified eigenvector.

For bottom-minus-top coordinates `w=(p,q,r)`, the scalar shift is
`u=Lx*p+Lc*q+r`; strictness means `-Lbottom<u<Ltop`. Repository `Packet.delta`
stores the negative vector, so the full original coordinate vector is
`-source.delta`. Centrality requires both letters to be `y` and
`|u|<1/2`. The closed central version `|u|<=1/2` is also proved: the
existing integral cubic lemma excludes both half-unit boundary values.

This work specializes the already reviewed
[central recurrence contract](bh-class-a-plus-upper-recurrence-stop-go-2026-11-15.md)
and the [written central theorem](class-a-plus-upper-central-recurrence-2026-11-15.md).
It introduces no new general shift-radix classification or claim of
novelty for the recurrence method.

### Derivation / reduction

#### 1. Construct the actual central orbit

For a complete central packet, define

```text
e = floor(beta*u+1/2),
i = 1+max(e,0),  j = 1+max(-e,0).
```

The full integral incidence image is itself an integral packet. Literal
scaling therefore transfers the cubic no-half-ties theorem to `beta*u`.
Consequently `|beta*u-e|<1/2`, with strict inequalities on both sides.
The existing upper RUN-range lemma proves `-n<=e<=n`, so `i,j` are actual
RUN ordinals in the two original `sigma(y)` words.

The child has the complete coordinates

```text
(2p+q+r,
 q+r,
 (n+d)p+nq+(n+1)r-e).
```

Its physical shift is `beta*u-e`, hence it remains central. In the
repository's stored sign convention this same update is
`delta' = M*delta + (0,0,e)`.

`CentralOrbit` records the actual packet at every depth, the actual two
occurrence indices at every edge, and its first integral coordinate.
`exists_literal_central_orbit` exposes the entire construction as an
unbundled existential statement. It assumes no orbit, projected recurrence,
finite graph, terminal cycle, or zero hit.

#### 2. Derive the scalar recurrence from those full packets

Writing `z_k` for the first coordinate gives

```text
z_0 = p,  z_1 = 2p+q+r,
w_(k+1) = yy(z_(k+1), z_(k+1)-2z_k,
              z_(k+2)-3z_(k+1)+2z_k).
```

The exact length row and centrality of `w_(k+1)` give

```text
|z_(k+2)+(2/beta)z_k+(beta-(n+4))z_(k+1)| < 1/2.
```

Thus the previously proved upper recurrence applies to the same literal
orbit. Both full packet reconstruction and recurrence derivation start
at the **first child**. Neither asserts the full cycle shape of the
original packet merely because its first scalar pair already alternates.

#### 3. Retain a quantitative tail start

Let

```text
B = (n+7)(|z_0|+|z_1|+1),
K = (2B+1)^2.
```

The existing forward bound confines each coordinate of the parity-changed
recurrence to `[-B,B]`. The new finite pigeonhole proof considers the
first `K+1` ordered pairs and finds a repeated pair with start `N<K`.
Strict-nearest uniqueness propagates that repeated pair to a periodic
tail. The existing high-`J` maximum argument or low-`J` cyclic energy
argument classifies that **same** tail as constant. No uncontrolled later
tail index replaces the bounded `N`.

In original coordinates, the tail alternates with amplitude `H>=0` and

```text
v*H < 1/2,  v=J/(beta+1).
```

The full packet is a signed `W_H=yy(H,3H,-6H)` at depth `N+1`. This
reconstruction delay still gives at most `K` literal nearest edges.

#### 4. Attach the existing complete cycle exit

The root upper bracket and amplitude imply

```text
JH < (beta+1)/2 < (n+7)/2 <= n,
JH <= n-1,  H <= n-1.
```

Those are precisely the range hypotheses of the existing complete
literal cycle exit. Its height recursion has at most `2H+1` edges. A
negative signed cycle uses full packet reversal and swaps both actual
occurrence ordinals at each edge. Reversal adds no substitution edge.

Therefore every central source with coordinates `(p,q,r)` has a path of
length at most

```text
C(n,p,q,r) = (2(n+7)(|p|+|2p+q+r|+1)+1)^2 + 2n-1.
```

The Lean natural-number form uses `Int.toNat` on the proved nonnegative
integer `B`. Typed zero also has an explicit empty completion theorem.
The general existence theorem does not promise a shortest path or the
executable constructor's first-zero/first-cycle cutoff.

#### 5. Concatenate entry at the identical full central packet

For an arbitrary strict source define its oriented positive boundary
margin

```text
m = Ltop-u       if u>=0,
m = Lbottom+u    if u<0.
```

Let `k` be the least natural number with `beta^k*m>=4`. The previous
literal entry theorem supplies `entry`, a complete central packet
`middle`, and both original tracks, with `length(entry)<=k+1`.

The new central theorem starts from this exact `middle` and supplies a
`suffix` of length at most `C(n,middle)`. Concatenation uses the identical
typed packet including its whole integral vector. Original-prefix
assembly is performed on `entry++suffix`, so neither prefix is reset at
the central join.

The combined bound is

```text
length(entry++suffix) <= (k+1) + C(n,middle).
```

The central term is evaluated at the **reached central packet**, not at
the original noncentral source. The theorem exposes the split, the
leastness of `k`, and each separate path instead of hiding this dependence.

#### 6. Authenticate the original tracks and strictness

`Completion` includes an `OrderedInteriorPath` to typed `y/y` zero,
`OriginalTraces` for exactly that transcript, and both original marked
prefixes satisfying

```text
M^t * (-source.delta) = P_t-Q_t.
```

The marks lie in the actual `t`-fold substituted original source letters.
The two `MarkTrace` lists are the projections of the same list of
occurrence pairs. Generic transport therefore retains the complete
identity at every selected edge; typed zero is full vector equality, not
only vanishing physical shift.

Positive literal scaling and the existing backward-interiority theorem
prove every packet on the concatenated ordered path strict. The central
orbit additionally records centrality at each nearest step.

### Evidence and replay

The source-bound gate is

```sh
tools/check_class_a_plus_upper_central_completion.sh
```

It copies project sources into a temporary workspace with no project
build artifacts, checks the exact Lean/Lake release and dependency pins,
reuses only the pinned upstream package cache, and rebuilds the complete
local dependency closure. Source and gate hashes are checked before and
after. The retained evidence records the actual local revision and all
receipts; no hosted green result is inferred from local checking.

The new audit independently expands the literal words, length row, full
offsets, both original tracks, delayed reconstruction and both budgets.
It checks 13 endpoint types and recursively audits every declaration
owned by the four new modules. Only `propext`, `Classical.choice`, and
`Quot.sound` are allowed. Its 44 contract refusals include missing and
wrong declarations, extra premises, dropped reconstruction delay, dropped
second initial coordinate, omitted original tracks, a weakened entry
bound and omitted leastness. Refusal of a changed type is an API check;
it is not automatically a claim that the changed proposition is false.

The gate also replays the existing entry, two-edge control, arithmetic
entry, upper recurrence, and full cycle-completion audit fixtures. The
canonical Mojo central constructor and independent exact oracle are
replayed at their declared finite source set. Counts, source hashes,
caps and raw receipts are recorded in the evidence packet.

The first isolated attempt compiled the new proof chain and passed its
new audit, then refused the next fixture because the gate had not built
the pre-existing `ClassAPlusUpperEntryControls` module. The corrected
gate adds that explicit build target. The initial script, failure log and
bindings are retained separately; its partial success is not counted as
the complete gate result.

### Negative controls

- **Reconstruction delay:** for every `n>=7,J=1`, `yy(1,2,-5)` is
  strictly central and its transformed initial scalar pair is `(1,1)`,
  but it is not any full `W` packet. The actual `(1,1)` RUN edge reaches
  `yy(-1,-3,6)=-W_1`. The new Lean control proves the full source
  distinction, actual edge, and centrality of both packets.
- **Nonzero nearest cycles:** the existing strict recurrence at
  `A=1/8,C=1` has a nonzero constant transformed solution. The retained
  Lean control prevents interpreting boundedness or scalar constancy as
  a zero hit. Productive literal cycle exits remain necessary.
- **Half ties:** the existing rational-coefficient tie at
  `A=1/8,C=1,a=4,b=0,c=0` still fails the strict nearest relation. The
  actual family uses its proved cubic exclusion; an arbitrary tie
  convention is not imported.
- **Both initial coordinates:** independent exact replay retains a
  central source with `p=0` whose next first coordinate already exceeds
  a reserve using `p` alone. The full source, literal indices, target,
  bounds and replay receipt are preserved in the evidence packet.
- **The y/c two-edge source:** the earlier universal control for
  `y/c(0,1,0)` is recompiled. Its actual path is
  `(n+2,0)` followed by `(1,2)`, and every one-edge central path is
  excluded. LAST `c` is never relabelled as RUN `y`.
- **Complete transport:** executable controls retain every offset
  coordinate, actual occurrence ordinal, original prefix and reversal
  track. Resource exhaustion or an ambiguous exact predicate refuses
  acceptance; finite replay is not substituted for the unbounded proof.

### Non-claims / remaining gaps

Within the displayed parameter chamber and actual strict integral source
domain, central-source completion and its assembly with entry are no
longer unresolved Lean premises. The strongest endpoint also discharges
root existence and positive literal scaling. The fixed-root convenience
endpoint still explicitly takes the bracket and cubic equation, as its
name and type indicate.

The result does not extend the smaller upper-member swap-seed certificates
to all strict sources, complete other family formalizations, discharge a
general tiling-realization or spectral interface, or prove universal BH,
residual A1-prime, general C4, or universal PSC. It does not identify the
general existential Lean path with the executable's earliest cutoff or
claim a source-independent entry bound. All governed claim statuses stay
unchanged. Hosted acceptance and independent human review of this local
candidate remain separate validation work, and nothing is published by
this increment.
