# Nonunit rank two with an injective endpoint map

**Status:** Written proof with a Lean-checked finite core
(`PscVerif.PeriodicPartnerTwinEndpoint`). Single prover, no independent verifier. It
continues the [trivial-stack note](c4-nonunit-trivial-stack-2026-11-21.md) and assumes no
strict system. No governed claim changes. Starting revision: `origin/main@4f32503`, with
the trivial-stack note.

## Statement

Let `σ` be a primitive substitution on three letters with irreducible Pisot incidence,
determinant other than `±1`, and coincidence rank two. Write `g_L`, `g_R` for the first-
and last-letter maps, and `L`, `R` for the left and right vertex sets of the eventual-range
graph `ER`.

**Theorem E.**
1. If `g_L` is injective, then `|R| ≤ 1`.
2. If `g_R` is injective, then `|L| ≤ 1`.

Equivalently: an injective endpoint map together with at least two letters on the opposite
side of `ER` rules out coincidence rank two.

## Work shown

### Assumptions and hypotheses

From the trivial-stack note, at `cr = 2` and nonunit determinant, with no strict system
assumed:

- **(T1)** The twin map `ι` (Barge, Lemma 13) is a continuous involution commuting with
  translation and inflation, and `ι(T)` is a fibre-mate of `T`.
- **(T2)** `T` and `ι(T)` share no vertex (Corollary V).

Also used:

- `ER` is connected for irreducible incidence (Lemma 7(2) of the
  [(F)-class note](c4-geometric-f-class-2026-11-16.md)). So `|E| ≥ |L| + |R| − 1`.
- (R3): vertices of fibre-mates within `δ₀` of each other are equal.
- Round-4 [Lemma A](c4-round4-2026-11-17.md#33-proofs) and its left mirror.

### Derivation / reduction

Take case 2; case 1 is the mirror through `PeriodicPartnerReflection`.

1. **A right vertex of degree two.** `|L| ≥ 2` and connectivity give two edges `ba`,
   `b′a` with the same right letter `a` (`exists_left_vertex_of_degree_two`, applied with
   the sides exchanged).
2. **Right-asymptotic seams.** The vertex tilings `T_(b,a)` and `T_(b′,a)` lie in `F₀`, are
   periodic, and agree exactly on `[0, ∞)`, since both continue with the periodic ray of
   `a`.
3. **Their twins are right-asymptotic.**
   - `T_(b,a) − t` and `T_(b′,a) − t` converge together as `t → +∞`.
   - `ι` is uniformly continuous and commutes with translation, so the same holds for the
     twins.
   - The twins are fibre-mates, so (R3) gives exact agreement on a right half-line.
   - They are distinct because `ι` is injective, and periodic because `ι` commutes with
     inflation.
4. **Branch at the origin.** By Lemma A the twins branch at a common vertex. With `g_R`
   injective the branch letters never merge, so the branch is at `0`
   (`vertex_of_injective`). So `ι(T_(b,a))` has a vertex at the origin.
5. **Contradiction.** `T_(b,a)` also has a vertex at the origin, so the twins share a
   vertex, against (T2) (`no_asymptotic_companion`). ∎

### What remains at nonunit rank two

At nonunit determinant and rank two, Theorem E leaves only two cases:

- `ER` is a single edge (`|L| = |R| = 1`, cycle rank zero, `dim H¹ = 3`);
- both endpoint maps are non-injective (or the matching opposite side has one letter).

In the second case every pair of seams sharing a ray has twins branching on the **collapsed
pair** of the matching endpoint map, strictly off the origin. This is case (B) of
[Theorem S](c4-witness-selection-2026-11-19.md#results), now realized by twins rather than
strict partners. The [(NM_V) census](c4-witness-selection-2026-11-19.md#the-residual-on-the-corpus)
shows that such interior–interior asymptotes do occur in zero fibres on the unit corpus.
So the residual configuration is not empty a priori.

### Evidence and replay

| Lean endpoint | Statement |
| --- | --- |
| `vertex_of_injective` | distinct periodic right-asymptotic tilings with an injective endpoint map both have a vertex at the origin |
| `no_asymptotic_companion` | under vertex-disjoint twins and an injective endpoint map, a periodic vertex tiling has no distinct periodic right-asymptotic companion |
| `exists_left_vertex_of_degree_two` | a bipartite edge set with at least two right vertices and `|L| + |R| ≤ |E| + 1` has a left vertex of degree two |

The twin involution, its continuity and the vertex-disjointness of twins enter the Lean
statements as hypotheses. They are the written results of the trivial-stack note.

```sh
cd proof/PscVerif && lake build PscVerif.PeriodicPartnerTwinEndpoint
lake env lean PeriodicPartnerAudit.lean
```

### Negative controls

- **Thue–Morse** has twins that share every vertex, so (T2) fails. Its endpoint maps are
  bijections on two letters, and its rank is two. (T2), which needs irreducible incidence,
  is indispensable.
- **Unimodular cubics** fall outside the trivial-stack theorem. Theorem E is not claimed
  for them.

### Non-claims / remaining gaps

1. The single-edge case and the case with both endpoint maps non-injective remain open at
   nonunit rank two.
2. Unit determinant and coincidence rank three or more are not covered.
3. Every step inherits the written inputs of #633 and of the trivial-stack note. Universal
   C4 and PSC remain open.
