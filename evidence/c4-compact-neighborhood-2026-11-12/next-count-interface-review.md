# Finite cut-count interface review

Read-only review, 2026-11-12, of
`/workspace/scratch/f96c28a561ad/psc-compact` at committed HEAD
`6915e8d592b7ea5cb7c6950249811e354dc6c3e7` (clean when inspected).
This is an addendum to `compact-next-count-plan.md`. Statements below are
**proposed proof interfaces**, not implemented declarations or compiled
acceptance. No repository source or build artifact was changed by this review.

## 1. Count reduction starts; a full enumeration of balanced cuts is unnecessary

Use the existing `Word := List (Fin 3)`, `WordPair := Word × Word`, and
`parikhZ : Word → (Fin 3 → ℤ)`. For `bs : List WordPair`, abbreviate

```text
topWord bs     = (bs.map Prod.fst).flatten
bottomWord bs  = (bs.map Prod.snd).flatten
topPrefix bs j = ((bs.take j).map Prod.fst).flatten
botPrefix bs j = ((bs.take j).map Prod.snd).flatten
factorStart bs (j : Fin bs.length) = parikhZ (topPrefix bs j.val)
startVectors bs : Finset (Fin 3 → ℤ) = Finset.univ.image (factorStart bs)
```

Only the last two need new public definitions. The `Fin bs.length` domain
retains occurrences, including repeated equal factors, and excludes the
terminal endpoint. It also avoids a false global injectivity statement for
`j : ℕ`, since `take j` stabilizes once `j ≥ bs.length`.

The sufficient finite set for the lower bound is
`Z := startVectors (red u v)`. It need only be a subset of the original
proper balanced-cut vectors. Proving that it enumerates *every* balanced
cut adds work without strengthening the required lower bound.

## 2. Minimal finite lemmas

The following signatures state the intended hypotheses and conclusions;
notation is abbreviated as above and names are provisional.

### A. Original-vector injectivity and cardinality

```text
factorStart_injective
  (hne : ∀ B ∈ bs, B.1 ≠ []) : Function.Injective (factorStart bs)

card_startVectors
  (hne : ∀ B ∈ bs, B.1 ≠ []) : (startVectors bs).card = bs.length
```

For `i < j ≤ bs.length`, the lengths of `topPrefix bs i` and
`topPrefix bs j` strictly increase: the intervening list contains a
nonempty top factor. Equal Parikh vectors would imply `Equiv1`, hence
equal ordinary word lengths. No balance, physical positivity, strictness,
irreducibility, rational independence, substitution, or Pisot assumption
is needed. `Finset.card_image` plus `Fintype.card_fin` then gives the count.

### B. Genuine full marks at the same starts

For `j : Fin bs.length`, under

```text
hne  : ∀ B ∈ bs, B.1 ≠ []
hbal : ∀ B ∈ bs, Equiv1 B.1 B.2
```

prove

```text
∃ top : Mark (topWord bs), ∃ bottom : Mark (bottomWord bs),
  top.before = topPrefix bs j.val ∧
  bottom.before = botPrefix bs j.val ∧
  parikhZ top.before = parikhZ bottom.before
```

The current factor is nonempty on both tracks, since balance gives equal
lengths. Split the list of factors at `j`, then split that factor at its
first letter; append the remaining factors to the two suffixes. This
constructs the entire `Mark.split` witnesses. Alternatively use `markAt`
after proving the corresponding proper prefix bounds. Prefix balance is
already `Binomial.equiv1_join` applied to `bs.take j`; it is not a missing
mathematical lemma. Both marks have the same ordinary index by balance.

### C. Physical sum bound

For arbitrary `ℓ : Fin 3 → ℝ` and `L : ℝ`,

```text
(∀ B ∈ bs, physicalLength ℓ B.1 ≤ L) →
  physicalLength ℓ (topWord bs) ≤ L * (bs.length : ℝ)
```

follows from `physicalLength_flatten` and a finite list sum inequality.
Together with A and `hne`, this gives

```text
physicalLength ℓ (topWord bs) ≤ L * ((startVectors bs).card : ℝ).
```

There is **no sign premise on `ℓ` or `L`** here. The cardinalities are equal.
If instead one enlarges to a finite set `Z'` with `startVectors bs ⊆ Z'`,
the implication to `physicalLength ℓ (topWord bs) ≤ L * (Z'.card : ℝ)`
does require `0 ≤ L` for monotone multiplication.

The smallest reduction-facing theorem consequently has precisely

```text
hbal   : Equiv1 u v
hbound : ∀ B ∈ red u v, physicalLength ℓ B.1 ≤ L
------------------------------------------------------------------
physicalLength ℓ u ≤ L * ((startVectors (red u v)).card : ℝ)
```

Use `red_isBlock hbal` for nonempty factors and `red_top hbal.length_eq`
for exact reconstruction. Do not omit the balance/equal-length contract:
`red` on arbitrary words is not a guaranteed complete balanced factorization.

### D. Physical strip, with the original origin

The cast identity
`offset ℓ (parikhZ w) = physicalLength ℓ w` follows directly from the
existing definitions (the integer coordinates are casts of natural counts).
Hence `offset ℓ (factorStart bs j) = factorBoundary ℓ bs j.val`.

A sufficient factor-level positivity premise is

```text
hpos : ∀ B ∈ bs, 0 < physicalLength ℓ B.1.
```

It gives, for each `j : Fin bs.length`,

```text
0 ≤ offset ℓ (factorStart bs j) ∧
offset ℓ (factorStart bs j) < physicalLength ℓ (topWord bs).
```

Indeed, the prefix is a sum of positive factor lengths, and the remaining
sum contains the selected positive factor. Global positivity of every
letter weight is sufficient but unnecessary for this generic statement.
For the named specialization, derive `hpos` from
`∀ a, 0 < ℓ a` and nonempty factors. The small helper
`w ≠ [] → 0 < physicalLength ℓ w` follows from `physicalLength_cons` and
`physicalLength_nonneg` and was not found as an existing declaration.

## 3. Strict specialization and the maximum

Given `strict : StrictSystem s C`, `T ∈ C`, and `k : ℕ`, set

```text
u = (subst s)^[k] T.1
v = (subst s)^[k] T.2
bs = red u v
```

`strict.equiv1` and `Descendants.equiv1_iterate_subst` supply full balance.
`strict.mem_of_red_iterate` puts every factor in `C`. Thus the reduction
bound needs only a supplied `L` satisfying
`∀ B ∈ C, physicalLength ℓ B.1 ≤ L`.

With strictly positive letter weights, choose
`Lmax := C.sup' strict.nonempty (fun B => physicalLength ℓ B.1)`.
This real maximum exists because `C` is finite and nonempty, and is
strictly positive because `strict.isBlock` makes every top word nonempty.
It is independent of `k` and of the selected source `T`. Use `sup'`, not
an assumed bottom element for `ℝ`.

The full marks from B, rewritten using `red_top` and `red_bot`, are
authenticated by existing `strict.cut_follow T-membership k top.split
bottom.split prefix-balance`. This returns **`CutPair C top.letter
bottom.letter`**, and `strict.cutPair_ne` gives distinctness. Thus the
represented carrier is exact. The named `strict_cut_labels` is an
alternative adapter at exponent `12*n`; a new theorem assuming merely
distinct letters would lose the represented-pair contract.

Empty cases are deliberate:

- `bs = []` gives `startVectors bs = ∅` and physical bound `0 ≤ 0`.
- Zero is included exactly when there is a factor (`j = 0`); terminal
  `j = bs.length` is always excluded. For nonempty balanced `u,v`,
  `red_ne_nil` supplies a factor and the initial vector is zero.
- An empty carrier has no `StrictSystem` because `strict.nonempty` is a
  field. The abstract list theorem still permits an empty list and needs
  no maximum. A maximum over an arbitrary empty carrier must not be used.
- Raw `StrictSystem` does **not** assume nonerasure. Inflated words can
  be empty, so strictness alone does not give positive total length or a
  nonempty set of cuts. Named nonerasure or exact positive scaling supplies
  that additional conclusion.

## 4. Named composition and the remaining analytic boundary

For fixture `f`, fixed `C`, `strict`, and `T ∈ C`, take `k = 12*n` and
`Z_n = startVectors (red u_n v_n)`. Extend the existing
`NamedGeometricEnclosure.physicalLength_subst` by induction on `k` for
arbitrary source words. Then

```text
X_n := beta^(12*n) * physicalLength physicalRow T.1
X_n ≤ Lmax * (Z_n.card : ℝ)
∀ z ∈ Z_n, 0 ≤ offset physicalRow z ∧ offset physicalRow z < X_n.
```

`physical_row_pos` and `beta_gt_two` give `X_n > 0` and divergence for
this fixed source. No source frequencies are needed. Rewrite between
`subst (iterateImages s k)` and `(subst s)^[k]` using the existing
**`StablePrefixWindow.subst_iterateImages`** (this is its actual source
module, not `OccurrenceResidue`).

For each fixed open `U` covering `carrierOverlap f C`, the committed
`eventually_carrierOverlap_strict_cuts_mem` has the order
`∃ N, ∀ n ≥ N, ∀ T ∈ C, ∀ actual top/bottom marks, ...`.
Applying B therefore gives one threshold, uniform over the fixed finite
carrier, such that

```text
∀ n ≥ N, ∀ T ∈ C, ∀ z ∈ Z_n(T),
  0 ≤ offset physicalRow z ∧ offset physicalRow z < X_n(T) ∧
  ambientStar (substitution f) piZ z ∈ U.
```

The threshold is uniform; the strip length `X_n(T)` may depend on the
source. This counts original integer vectors throughout. Neither the
ambient image `cutPoints` nor the auxiliary anchored prefix witnesses
require an injectivity claim, because their cardinalities are never used.

For a later upper lattice count, choose `U` with bounded stable projection
(for example a fixed bounded regular cylinder union). An arbitrary open
neighborhood need not have finite lattice occupancy. Prove finiteness of
the integer strip/window set before taking its cardinality, and keep `U`
and its residue depths fixed before the large-`X` limit. Covolume,
fixed-origin equidistribution, and regular outer measure approximation
remain separate obligations; none follows from this finite interface.

## 5. Reuse versus genuinely missing work

Repository paths are under `proof/PscVerif/PscVerif/`.

| Existing source | Reusable declarations |
| --- | --- |
| `Binomial.lean` | `equiv1_join`, `Equiv1.length_eq` |
| `Reduction.lean` | `red_top`, `red_bot`, `red_ne_nil`, `red_isBlock` |
| `OccurrenceTransport.lean` | `Mark`, `Mark.index_lt`, `parikhZ`, both `Equiv1`/Parikh conversion lemmas, `offset` |
| `OccurrenceFinite.lean` | `markAt`, `markAt_before`, `markEquiv` |
| `OccurrenceNewborn.lean` | Physical additivity, flattening, nonnegativity, `factorBoundary`, `factorBoundary_succ` |
| `StrictSystem.lean` | `mem_of_red_iterate`, `cut_follow`, `cutPair_ne`, nonempty carrier and block fields |
| `Descendants.lean`, `StablePrefixWindow.lean` | `equiv1_iterate_subst`, `subst_iterateImages` |
| Named chart/enclosure/neighborhood modules | Positive row, exact one-step scaling, represented-carrier eventual containment |

The genuinely missing finite content is the occurrence-indexed integer
start set, its prefix-length injectivity/cardinality, the genuine start
marks, the bounded physical sum and strip wrappers, and the whole-word
power-scaling adapter. Existing prefix balance and strict label theorems
should be reused. `StrictSystem.mismatch_density` counts mismatched
positions, not balanced cuts. `PscVerif.PhysicalMass` proves finite graph
transpose-budget identities; it supplies no word-length or lattice-count
lemma and is not needed for this next finite module.

This review records no theorem acceptance and promotes no M1, overlap
positivity, C4, or PSC claim.
