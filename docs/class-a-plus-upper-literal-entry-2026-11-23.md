# Upper plus-Class-A literal entry: local Lean completion

This is an unpublished local continuation of the
[November 16 all-source entry proof](class-a-plus-upper-all-source-entry-2026-11-16.md).
The base checkout is accepted head `1bdaa34c63e6de97a0f17998c4f06887a18f099c`,
whose tree `225e933c2ca2d8aaa8be550c003e824ac93fa201` is exactly the tree of
current main merge `7bfcd8c15e845f148b3c0ee405ca839ae6039e2d` (PR #654).
No branch, PR, comment, or repository change has been published for this work.

## Work shown

### Assumptions and hypotheses

Let `n,d : ℕ` satisfy `7 ≤ n`, `n+5 ≤ d`, and `d ≤ 2*n+11`.
The substitution uses the original words, with letters in `(x,c,y)` order:

```text
sigma(x) = x y^(n+d) x
sigma(c) = c y^n x
sigma(y) = x y^(n+1) c
```

Set `J=2*n+12-d`. The Lean development proves existence of a real root
`n+4 < beta < n+6` of

```text
beta^3 - (n+4)*beta^2 + (n+5-d)*beta - 2 = 0.
```

It defines `X=beta-n-2+1/beta`, `K=1-1/beta`, and `Ly=1`, and proves positivity,
the bounds `2<X<10/3`, `10/11<K<1`, and exact length scaling for the literal
words. No caller supplies irreducibility, absence of ties, image scaling,
positivity, a finite carrier, an entry path, or a central coincidence theorem.

The arbitrary source is a complete integral `Packet`: two actual letter
types and all three integer offset coordinates. The occurrence infrastructure
stores top-minus-bottom `delta`; the manuscript displacement is `w=-delta`.
Its scalar shift is `u=-offset lengths delta=Xp+Kq+r`. The source hypothesis
is precisely strict overlap, `-Lbottom<u<Ltop`.

For a fixed supplied `beta`, `all_source_entry_nd` explicitly retains the
root equation and its bracket. The stronger `exists_root_all_source_entry`
constructs such a root for every permitted `n,d` and then quantifies over
all strict integral sources. An additional identification with an independently
defined Perron-root object is not needed for this literal entry statement.

### Derivation / reduction

#### 1. Integral cubic obstruction to half ties

`ClassAPlusUpperNoHalfTies.polyQ_irreducible` derives irreducibility of
`T^3-(n+4)T^2+(J-n-7)T-2` over `ℚ`. The monic rational-root theorem restricts
any rational root to the integral divisors of `2`; the actual parameter
inequalities exclude all of them. Degree three then gives irreducibility.

Consequently, a rational quadratic vanishing at `beta` has every coefficient
zero. If the full integral shift `Xp+Kq+r` were `z+1/2`, multiplication by
`2*beta` would produce the quadratic with coefficients

```text
2*p,
2*(q+r-(n+2)*p)-2*z-1,
2*(p-q).
```

The middle coefficient is odd and cannot vanish. This proves
`vector_shift_ne_half_integer` for every integral `(p,q,r)` and integer `z`.
The direct-entry proof applies this theorem to the actual complete inflated
child packet at the first RUN marks. It never substitutes a projected offset.

#### 2. Literal RUN and boundary children

`ClassAPlusUpperLiteralEntry.direct_entry` instantiates the existing
`ordered_run_indices` gap theorem with actual RUN lengths and proper-prefix
marks. Its two indices lie in the original words and its complete target
is the affine child of those marks. Centrality is strict: the result has
type `y/y` and `|u|<1/2`.

The same module proves three literal boundary-child formulas:

| Selected indices | Child type | Scalar displacement |
| --- | --- | --- |
| `(Rtop+1,0)` | `LAST(top)/FIRST(bottom)` | `G-D` |
| `(Rtop,0)` | `y/FIRST(bottom)` | `G+1-D` |
| `(Rtop+1,1)` | `LAST(top)/y` | `E-D` |

Here `D=beta*(Ltop-u)`, `G=L_LAST(top)`, `F=L_FIRST(bottom)`, and `E=G+F`.
`oriented_alternative` instantiates the existing five-way arithmetic boundary
lemma with exactly those marks. It supplies either a central entry of at most
two actual edges, or one strict nonnegative child whose boundary distance
is exactly `beta` times the preceding one.

#### 3. Source-dependent termination and full orientation

`ClassAPlusUpperEntryBound` instantiates `bounded_entry_of_growth` on states
containing a normalized complete packet and a separate reversal bit. Each
state edge projects to an actual `IndexedDigitStep` on the original tracks.
The reversal bit is preserved on a growth edge, including a child with zero
scalar shift. Thus a change of comparison orientation never inserts an edge
or accidentally changes which boundary distance is being multiplied.

For the initial source, choose its original orientation when `u≥0`, and
otherwise reverse both full tracks. Let `m` be the positive distance to the
right boundary of the oriented top tile. Every such margin is less than `4`.
The least natural `k` with `beta^k*m≥4` exists, and
`least_entry_power_spec` proves both its threshold and leastness.

The fixed-root endpoint is:

```text
all_source_entry_nd:
  every strict integral source has a central endpoint and an actual transcript
  of at most k+1 edges, for that least k, together with OrderedInteriorPath
  and OriginalTraces for the same transcript.
```

`exists_root_all_source_entry` also constructs the bracketed root and its
positive exact literal scaling, so root existence is not an unresolved premise.
An already-central source has a separately proved empty-path witness.

#### 4. Original occurrences and complete offsets

`ClassAPlusUpperEntryTransport` reuses the existing `OrderedPath`,
`OrderedInteriorPath`, and `MarkTrace` definitions. It constructs actual
marks in each original iterated source-letter word. Both tracks retain every
local ordinal, accumulated prefix word, selected letter, and suffix.

For a transcript of length `t`, `OriginalTraces` retains the full equation

```text
target.delta = M^t * source.delta + P - Q.
```

In the manuscript convention this is `w_t=M^t*w_0+Q-P`. Reversal swaps the
two complete marks and index lists and negates all three offset coordinates,
while preserving `t`. The target offset is retained even when nonzero.
No assertion of target zero is used in the entry theorem.

### Evidence and replay

The new formal modules are:

- [`ClassAPlusUpperNoHalfTies.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperNoHalfTies.lean)
- [`ClassAPlusUpperLiteralEntry.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperLiteralEntry.lean)
- [`ClassAPlusUpperEntryTransport.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperEntryTransport.lean)
- [`ClassAPlusUpperEntryBound.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperEntryBound.lean)
- [`ClassAPlusUpperEntryControls.lean`](../proof/PscVerif/PscVerif/ClassAPlusUpperEntryControls.lean)

The local acceptance script copies source and configuration into an empty
project workspace, verifies the pinned upstream package sources, reuses
only their existing build cache, rebuilds every project module in the target
import closure, and runs the independent endpoint/axiom audit and both control
fixtures. It records and rechecks SHA-256 bindings for every copied Lean source
and project pin, and refuses changed sources or missing audit completion.

```sh
tools/check_class_a_plus_upper_literal_entry.sh
```

This requires the exact `lean-toolchain` release on PATH and populated
manifest-pinned upstream dependencies. `PSC_ENTRY_PACKAGES` may name the
existing pinned package cache; `PSC_ENTRY_EVIDENCE_DIR` selects the receipt
directory. The gate does not copy any project `.olean` into its fresh workspace.

The existing exact executable replay remains unchanged:

```sh
(cd kernel && MODULAR_TELEMETRY_ENABLED=0 MODULAR_CRASH_REPORTING_ENABLED=0 \
  pixi run --locked mojo run -I . tests/test_class_a_plus_upper_entry.mojo --emit) \
  > /tmp/psc-upper-entry-native.txt
python3 oracles/python/class_a_plus_upper_entry_independent.py \
  --native /tmp/psc-upper-entry-native.txt \
  --transcripts /tmp/psc-upper-entry.jsonl
python3 oracles/python/class_a_plus_upper_entry_independent.py \
  --replay-transcripts /tmp/psc-upper-entry.jsonl
```

The fresh receipt details and source hashes are recorded in the
[local acceptance packet](../evidence/class-a-plus-upper-literal-entry-2026-11-23/README.md).
A successful finite entry-plus-central replay does
not establish the remaining universal central-source Lean theorem. No hosted
CI run has been requested for these unpublished changes; #654's hosted results
belong to its own revision and do not certify this patch.

### Negative controls

The source `y/c (0,1,0)` is universally strict in the chamber and is not already
central. `one_edge_central_impossible` proves that **every** one-edge literal
occurrence pair fails to produce a central target. Any central target would
require two RUN `y` marks; classifying those actual marks gives output shift
at least `2K>1/2`.

`two_edge_strict_path` proves the exact successful path:

```text
y/c (0,1,0) --(n+2,0)--> c/c (0,1,-1) --(1,2)--> y/y (0,0,0).
```

The middle shift is `-1/beta`. Both original tracks are constructed explicitly,
with top indices `[n+2,1]` and bottom indices `[0,2]`. Their complete prefix
coordinates are

```text
P=(n+3,n+2,n+d+(n+1)^2), Q=(0,1,1), M^2*(0,1,0)=P-Q.
```

`wrong_last_index_rejected` proves that replacing the first top index by
`n+1` cannot produce top type `c`, for any supplied offset: it is a RUN `y`.
The exact executable controls also retain altered-coordinate, truncated-path,
touching-child, and changed-original-prefix rejections. The independent
reversal replay compares complete states, indices, depths, and both prefixes.

### Non-claims / remaining gaps

The entry-specific obligation is discharged by the local Lean development.
The endpoint is a strict central `y/y` packet with its full offset, which may
be nonzero. The next mathematical assembly remains the end-to-end **central-source
coincidence** theorem: instantiate the central nearest recurrence and its
reconstruction at this exact endpoint, join its signed cycle completion, and
append those same literal indices and original tracks to typed zero.

No universal BH, residual A1′, general C4, or universal Pisot-substitution
claim is promoted. The existing 70 smaller-member certificates retain their
documented complete swap-seed scope; this n≥7 theorem does not widen them.
This work uses the already reviewed November 16 source/hypothesis decision,
and makes no new general spectral claim. Independent human review remains
pending, separately from the mechanical acceptance.
