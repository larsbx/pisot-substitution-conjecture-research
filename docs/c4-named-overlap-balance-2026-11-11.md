# Exact overlap balance on the named finite carriers

## Scope and status

This continuation starts from merged #548, main
`765bb39c83035b5ccacbc8115ecc26acc4111865`. That revision constructs the
actual prefix tiles, finite incoming domains, and correctly normalized
product-Haar scaling for the two substitutions `1/021/001` and `1/012/001`.
The [source check](c4-named-overlap-balance-literature-2026-11-11.md) precedes
the implementation. The implementation and exact-revision verification
record below must be read separately; a source statement is not a build receipt.

The target of this increment is an **exact overlap recurrence** on the same
finite domains. A positive loss certificate and the strict-cut positive
measure implication remain separate. No governed claim is promoted.

## Assumptions and hypotheses

Choose one named fixture `f : Fin 2`, an even substitution exponent
`k = 2r`, and either its full `packets f` domain or its nondiagonal
`strictPackets f` domain. These are the finite sets constructed from the
authenticated real chart and actual prefix enclosures. Their natural
coordinate bounds are mathematically chosen from proved bounds. They are
not declared equal to a serialized historical graph.

Use the original product of the real stable chart with the compatible
matrix-adic group `H_M`. The compact factor carries a normalized additive
Haar measure; the stable factor carries the already fixed coordinate
Lebesgue measure. Both actual period-two words and every literal parent
and occurrence position remain part of the construction.

For a packet `p`, write `O(p)` for its actual compact overlap, and set

```text
v(p) = mu(O(p)),                     compact product-Haar measure,
h(p) = packetMass(physicalRow, p),   physical interval overlap length,
theta = beta^k.
```

Every `v(p)` is finite and nonnegative. Every `h(p)` in either domain is
strictly positive because membership includes strict physical interior.
These are different functions: physical positivity does not prove
positive compact overlap measure.

## Derivation / reduction

### 1. Reverse complete literal occurrences, not target sets

For represented packets `u,p`, define

```text
F(u,p) = number of actual position pairs (i,j) in sigma^k(u.top),
         sigma^k(u.bottom) whose forward digit packet is p,
T(p,u) = F(u,p).
```

The equivalence between a literal inverse occurrence and its two forward
positions preserves both round trips. Grouping the complete incoming
occurrence sum by its ancestor packet therefore gives `T v`. Two position
pairs with the same endpoint contribute twice. There is no quotient by
track swap, so orbit-size assumptions are not needed for this increment.

### 2. The actual Haar cover supplies the lower matrix bound

The existing incoming cover represents every nonempty piece, and each
affine image under the block action has measure `beta^(-k)` times the
ancestor overlap measure. Finite-union subadditivity gives

```text
theta v(p) <= sum_u T(p,u) v(u).
```

This uses the genuine tile equation, original matrix-adic range reflection,
finite carrier representation, and normalization already proved for these
named systems. They are not new caller-supplied hypotheses.

### 3. Physical subdivision supplies the upper transpose bound

The complete forward positional subdivision has total physical mass
`theta h(u)`. Retaining only children in the finite domain can decrease
this total, because every physical child mass is nonnegative. Hence

```text
sum_p F(u,p) h(p) <= theta h(u),
or equivalently T^t h <= theta h.
```

No forward-closure assumption is used. The difference is exactly the
physical mass omitted by restricting the full literal row, rather than a
guessed spectral slack or a count of omitted endpoint labels.

### 4. Finite dual conservation forces equality

Let `s = T v - theta v` and `d = theta h - T^t h`. Both vectors are
nonnegative. Finite double counting gives

```text
sum_p h(p) s(p) + sum_p d(p) v(p) = 0.
```

Every summand is nonnegative and every physical weight is strictly
positive. Therefore

```text
T v = theta v,                 exact overlap recurrence,
d(p) v(p) = 0 for every p.     loss annihilates overlap measure.
```

This reuses `PhysicalMass.saturation` and `products_zero`. No measure
disjointness is assumed to obtain equality. An a.e. disjointness corollary
would require its own finite-measurable-family argument and is not silently
identified with setwise disjointness.

### 5. Consequences preserve the inverse graph orientation

An edge `p -> u` means an actual inverse ancestor occurrence. The exact
recurrence makes a zero overlap at `p` force zero at each such `u`.
A genuine positive-deficit vertex therefore forces zero at every vertex
reachable from it. If each source strongly connected component contains
such a vertex, every overlap in the domain is null.

Conversely, a nonzero overlap has a source-component ancestor on which
every deficit is zero. This is a necessary obstruction to the loss
argument; it does not construct positive measure on a conservative source.
Loss in sink components is insufficient in this orientation.

## Evidence and replay

The canonical acceptance gate is the full isolated-source Lean build and
compiled declaration/axiom audit, together with the generated inventory:

```bash
./tools/check_lean.sh
python tools/make_proof_bank.py --check
```

Existing independently implemented controls exercise the physical
subdivision, transpose orientation, multiplicity, and finite dual theorem:

```bash
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_mass.mojo)
(cd kernel && pixi run --locked mojo run -I . tests/test_c4_overlap_physical_mass.mojo)
python tools/check_c4_overlap_mass_quint.py --output /tmp/c4-overlap-mass-quint
python tools/check_physical_mass_quint.py --output /tmp/physical-mass-quint
```

These executable checks retain their existing finite scopes. They are
regression evidence for reused contracts, not a decoder of the newly
constructed noncomputable domain. The direct Lean proof is the binding
between literal occurrences and the named Haar measures.

## Negative controls

- Repeated occurrences cannot be replaced by endpoint support. Deleting a
  duplicate can fabricate a loss and invalidate the actual cover.
- Reversing the transpose or replacing source components by sinks changes
  the conclusion; the existing adversarial models preserve these witnesses.
- Zero physical weights can hide a positive slack, so physical interior is
  essential for the saturation step.
- Nonempty compact sets may have zero Haar measure. Neither exact balance
  nor a conservative source supplies strict-root positivity.
- At exponent zero the literal transition is the identity. It is a
  conservative control, not a source-loss certificate.
- Complete strict child closure retains every positive physical child.
  `OccurrenceMassStrict.full_forward_conservative` remains in force and
  prevents deriving a loss from strictness alone.

## Non-claims / remaining gaps

The next actionable certificate obligation is to bind an executable finite
**nondiagonal domain** to these exact literal geometric rows, then produce
actual positive losses reaching the required strict roots, or exclude the
remaining conservative source components by an appropriate exact certificate. The accepted
historical graph data cannot be substituted until that domain/row refinement
has been proved.

The full domain is not a useful whole-domain source-loss target. It retains
the three diagonal packets. Every positive physical forward child of a
diagonal packet is diagonal and retained, hence its deficit is zero.
Nondiagonal interior packets cannot have diagonal inverse ancestors. Thus
the finite diagonal subgraph contains a conservative source component of
the full graph. This is a derived review observation from the existing
diagonal transport and the new omitted-mass identity, not a separately
formalized no-source-loss theorem in this increment. Full-domain balance
remains useful; the dedicated nullity consumer targets `strictPackets`.

For a C4 contradiction, an assumed finite fully strict balanced-pair system
must still yield a positive compact cut set covered by the represented
strict roots, with the same measure normalization. Membership in
`strictPackets` does not construct that system or that positive set.

The extension to arbitrary standing PIP substitutions, universal
productivity, C4, BH, A1', G1, Concentration and PSC remains open. Human
review remains validation debt, rather than a new research-progress premise.
