# Minus-Class-A literal arithmetic, central escape and original prefixes

Date: November 14, 2026. Baseline: draft PR #579,
`110e7e9ef8243bc24adf80d6e8a375add586d850`; current main inspected at
`a19670c521927a8f6ac7e08f26cd3d563eafdce3`.

## Result and exact source scope

This increment connects the literal lower-chamber substitution to the
abstract constant-tail recurrence and to complete original-prefix witnesses.
Its principal compiled target concerns **every central integral y/y source**
for `d>=5,n>=d+1`. It does not assume cyclicity, seed reachability, a finite
carrier, a supplied recurrence, a supplied periodic tail, a supplied height
bound, or a no-half-unit assertion. The actual source centrality condition
remains explicit. The all-strict-source density entrance is still a separate
formal obligation.

The exact-revision evidence and the distinction between local development,
fresh source-isolated and hosted acceptance are recorded in the
[evidence packet](../evidence/class-a-minus-literal-lean-2026-11-14/README.md).
This note changes no governed BH or PSC claim status.

## Work shown

### Assumptions and hypotheses

The words are unchanged:

```text
sigma(x)=x y^(n+d) x
sigma(c)=c y^n x
sigma(y)=x y^(n-1) c
d>=5, n>=d+1.
```

Let `beta` satisfy the literal cubic

```text
beta^3-(n+2)beta^2+(n-d-1)beta+2=0,
n+1<beta<n+2.
```

`root_exists` proves existence of such a root by the intermediate value
theorem, uniformly throughout this chamber. The proofs retain an explicit
`RootData` argument so the same root is used in every length, bound and
occurrence theorem. It is not a caller-supplied unverified numerical root.

Normalize `Ly=1`, `Lc=1+1/beta`, and `Lx=beta-n-1/beta`. A source is
`(y,y,p,q,r)` with all three coordinates integral and

```text
|Lx*p+Lc*q+r|<=1/2.
```

The manuscript uses bottom-minus-top displacement. The existing Lean
`Packet.delta` convention is its negative; the literal `packet` constructor
performs that sign change. All final source identities convert it back.

### Derivation / reduction

#### 1. Literal arithmetic and half-unit exclusion

`ClassAMinusLiteralArithmetic` proves positive lengths, all three actual
image-word scaling equations and

```text
1-2/beta-(n+2-beta)=d/(beta-1)>0.
```

Thus `A=2/beta` and `B=n+2-beta` satisfy the abstract recurrence's exact
conditions `0<=A<1/2`, `0<B`, and `A+B<1`. A constant tail's amplitude
condition implies the integer bound `2*d*abs(H)<=n`; that bound is derived
before the original three-RUN descent is invoked.

`ClassAMinusNoHalfUnit` proves the parameterized cubic irreducible over the
rationals by its monic rational-root test, excludes every nonzero rational
quadratic at the bracketed root, and excludes every odd half-integer physical
displacement for every integral triple. In particular centrality `<=1/2`
strengthens to `<1/2`. No floating approximation supplies rounding uniqueness.

`ClassAMinusRootSpectrum` derives the characteristic polynomial from the
actual literal word counts. It proves that the normalized lengths form a
strictly positive eigenrow, that the bracketed root is greater than one,
and that every other complex characteristic root has norm strictly less
than one. `literal_pisot_root_exists` combines these facts with existence.
This discharges the literal algebraic Perron/Pisot identification; it asserts
no dynamical spectral conclusion.

#### 2. Actual RUN selection supplies the recurrence

`ClassAMinusCentralBridge` defines the complete integer state and selects

```text
g=-floor(beta*u+1/2)
top original ordinal=(-g).toNat+1
bottom original ordinal=g.toNat+1.
```

The selector's strict error and `n>=6` place both positions in the actual
`y` runs, before LAST. Its full successor is

```text
(2p+q+r, q+r, (n+d)p+nq+(n-1)r+g).
```

The physical displacement is exactly `beta*u+g`, so the deterministic
selector remains central. Its first coordinates satisfy the existing strict
nearest recurrence. After one step the next complete packet is recovered
from three consecutive first coordinates, not just a projected label.
The existing eventual-constant theorem therefore produces a genuine
`U_H=(y,y,H,-H,0)`. The derived amplitude bound authorizes the original
three-RUN height descent, including negative heights through track reversal.

The public `literal_central_composable_path` concludes typed coincidence
through finite actual interior steps. It has no separate recurrence,
periodicity, contraction, finite-carrier or no-tie premise.

#### 3. Complete original occurrence assembly

`ClassAMinusPrefixAssembly.OrderedPath` retains the finite ordered list of
original top and bottom occurrence indices. Concatenation requires equality
of the full middle packet. At each step the new prefix word is exactly the
substitution of the previous prefix followed by the selected local prefix.
`MarkTrace` explicitly binds both constructed marks to every ordinal in
their respective tracks. `OrderedInteriorPath` retains those same indices
and the strict-interior property at the source and every intermediate packet.

For any such path of length `m`, the module constructs actual marks in
`sigma^m(source.top)` and `sigma^m(source.bottom)` and first proves

```text
terminal.delta=M^m*source.delta+Parikh(topPrefix)-Parikh(bottomPrefix).
```

Only after retaining this arbitrary terminal offset does it specialize
to zero. `literal_central_traced_prefixes` supplies one ordered interior
path, both marks with their complete `MarkTrace` witnesses, both terminal
letters equal to `y`, and the complete original identity `M^m w=P-Q`.
The indices used in that path are the indices used in both prefix traces.
The weaker projection `literal_central_original_prefixes` is also retained.

`source_with_traced_central_descendant` accepts an actual ordered entry path from
an arbitrary original packet to a central packet and appends the proved
central escape at that identical packet. The final prefix identity remains
based at the original source; both mark traces use the original entry list
followed by the escape list, in that order. This is the precise consumer for
the remaining all-source entry proof; its entry-path premise stays visible.

#### 4. Density and finite packing

`ClassAMinusDensity` proves the literal one-level counts, their physical
lengths, and all three simultaneous density inequalities. It sums the
inequalities over any finite concatenation of original image blocks and
proves the strict reserve

```text
Y-2X-2C>1/12,
Y=(n-1)/beta, X=2/(beta*Lx), C=1/beta.
```

Its finite packing theorem retains individual centers and assigned tile
identities: a closed tile of length less than two contains at most two
centers separated by at least one. Summing assignment fibers and allowing
two boundary tiles gives `Ny<=2Nx+2Nc+4`.

The literal count contradiction proves these estimates incompatible when
the common interval length `J>=240(n+1)`. The threshold-existence theorem
proves that every positive source overlap length eventually reaches that
threshold under inflation; it does not claim a source-independent depth.

The remaining formal interface is constructive: form the actual full/partial
image-block decomposition of the two inflated words, prove its boundary
budgets, and, under absence of a central pair, construct the center-to-non-y
tile assignment. Then use the actual selected occurrences to obtain the
ordered entry path consumed above. The count inequalities and assignment
premises in the present theorems are explicit, not discharged by finite
regression fixtures.

### Evidence and replay

The new formal modules have a dedicated source-isolated compile and exact-type
audit. The audit checks all owned declarations against the three permitted
standard Lean axioms and independently checks the public endpoint types,
including rejection of missing, wrong-typed and extra-premise substitutes.
The repository-wide root import and generated proof bank include the new
modules. See the evidence packet for the exact source manifests and outcomes.

The unchanged canonical Mojo and independent Python layers continue to have
their existing scopes. Replaying their finite original-prefix certificates
does not establish the all-source geometric interface.

### Negative controls

- Out-of-chamber parameters cannot enter the literal lower-chamber theorem.
- Equal prefix lengths and identical terminal letters do not imply the full
  three-coordinate prefix identity; the countercontrol uses genuine marks.
- A wrong transcript of the same length is rejected even when the source,
  terminal letter and complete zero-prefix identity agree. The positive
  control uses the actual index-zero occurrence of the identity substitution;
  its index-one replacement has no `MarkTrace` witness.
- Two individually valid edges with the same tile labels and ordinals but
  different middle packets cannot be concatenated.
- An empty transcript cannot erase a nonzero original offset.
- Integral offset zero with different letters is not typed coincidence.
- Three centers at `0,1,2` fit in a closed interval of length exactly two;
  the strict short-tile bound is necessary.

Existing independent controls for invalid word bindings, original ordinals,
full offsets, premature terminalization and incomplete path/source sets are
retained. The new formal existence paths do not additionally claim the
production constructor's first-hit terminalization policy.

### Non-claims / remaining gaps

The all-strict-source central-density entry is not yet connected end to end
in Lean. The immediate next mathematical obligation is the actual interval
decomposition and assignment described above, followed by ancestry extraction.
The inherited seed-only regions retain their original quantifiers.

This family-specific formal advance is not universal BH #139, residual A1',
C4, a spectral theorem for a full dynamical system, or the Pisot substitution
conjecture. Local cached compilation is not fresh source-isolated or hosted
acceptance. Independent mathematical review and merging remain with the user.
