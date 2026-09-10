# Proof ladder

## Stable Level 2 — unique decodability

Proved:

1. `det M_sigma != 0` gives letter injectivity.
2. The defect theorem gives unique decodability of the image code `{sigma(a)}`.
3. Unique decodability for powers gives a unique supertile hierarchy inside supertiles.

Not proved:

4. ~~Pisot growth gives predecessor contraction and hence finite `B_sigma`.~~ **Withdrawn.** The inequality `beta * L(s') <= L(s) + D` is false; the observed worst ratio is 8.0 and the excess is unbounded. Global BPA finiteness remains G1 in the repository architecture.

## Level 3 — current proof architecture

The global open theorem remains:

> **C1 / SCC Producer.** Every recurrent noncoincident SCC of `B_sigma` is productive.

The useful finite graph normal form is narrower.

### Sink-SCC reduction

Let `NP` be the states from which no coincidence is reachable. `NP` is forward-closed. If `B_sigma` is finite and `NP` is nonempty, the condensation DAG of the induced nonproductive graph has a sink SCC. That SCC is closed, recurrent, noncoincident, and nonproductive.

Therefore G1 is used to extract a finite strict counterexample component. One does **not** need synchronization of every recurrent SCC.

### Boundary/locality sufficiency chain

The Boundary Synchronization Lemma says that a synchronizing zero-return boundary yields a coincidence after finitely many endpoint-map iterates. `docs/c3-locality-reduction.md` proves that higher-inflation newborn synchronization localizes to a one-step newborn cut in an irreducible state of the same closed SCC.

The present one-way proof route is therefore

```text
C4 => C3-local => C2 => C1.
```

These are sufficiency arrows. No converse is claimed.

## Proved C4 structure on a finite closed counterexample component

Assume a finite closed nonproductive recurrent noncoincident SCC `C` is given. Write `N=N_C` for unsigned child incidence.

### Endpoint quotient

- The 27 endpoint self-maps on three letters have seven conjugacy types A–G.
- A/B are globally synchronizing.
- If either `sigma_+` or `sigma_-` is globally synchronizing, every balanced pair is productive; this theorem needs neither Pisot nor G1.
- Eventual endpoint synchronization is an equivalence relation and the induced map on quotient classes is a permutation.
- The projected endpoint state signature has at most 1, 3, or 9 values depending on the two quotient sizes.

### Parikh quotient and exact Perron equality

Let `P_C` have state Parikh vectors as columns. Then

```text
P_C N_C = M_sigma P_C.
```

For irreducible cubic `chi_M`, the nonzero rational image of `P_C` is all of `Q^3`. Hence

```text
rank P_C = 3,
|C| >= 3,
chi_M divides chi_N,
rho(N_C) >= beta.
```

Because the component is **closed**, its child counts account for the entire substituted mass. The positive Perron left eigenvector of `M_sigma`, pulled back through `P_C`, gives a positive left eigenvector of `N_C` with eigenvalue `beta`; therefore

> **For a strict closed nonproductive component, `rho(N_C)=beta` exactly.**

This supersedes the old v34 lower-bound emphasis in this counterexample regime. The v34 estimate remains useful for other closed/leaking configurations but is not the sharp statement here.

### Orientation and signed defects

Normalizing `(u,v)~(v,u)` hides a `Z/2` orientation cocycle. If `A` and `B` count positive and reversed child occurrences,

```text
N=A+B,
S=A-B.
```

The oriented double-cover incidence splits into deck-even `N` and deck-odd `S`, so `rho(S)<=beta`. Equality is rigid (gauge/anti-gauge in the primitive case).

At the first nonzero scattered-subword defect degree `r`, the defect columns satisfy a signed intertwiner

```text
Q_r S = Phi_r Q_r.
```

In particular:

- degree 2: `Q2 S=(Lambda^2 M)Q2`; if nonzero in a strict component, the exterior-square cubic occurs in the odd sector;
- degree 3 with `K2=0`: `Q3 S=Phi3 Q3`, and low growth forces the image into the two-dimensional determinant/centralizer sector;
- degree 4: every rational free-Lie factor has spectral radius at least `beta`, with equality only in specified unimodular/extremal cases;
- arbitrary degree: the generalized-Witt/mod-3 sieve leaves only near-balanced Galois weight families as possible low-growth sectors.

### Degree-2 arithmetic and factorization layers

Since `N congruent S (mod 2)`, the characteristic polynomial of a degree-2 strict component over `F2` must contain both the reduced cubic of `M` and that of `Lambda^2 M`. This gives the exact SCC-size lower-bound table `{3,4,5,6}` recorded in `docs/c4-degree2-parity-sieve.md`.

The fixed-endpoint `K2` half-space route is retired: explicit same-endpoint irreducible states positively span the origin.

The next genuinely new information is **ordered child factorization**. For word area

```text
a(w)=(N12-N21, N13-N31, N23-N32)
```

and state mid-area `H(T)=a(u)+a(v)`, every actual ordered zero-return factorization satisfies

```text
(Lambda^2 M)H + 2 C_sigma P = HN + 2 Omega_tau.
```

`Omega_tau` depends on child order, so this identity detects synthetic signed templates that every preceding incidence/spectral/endpoint invariant accepts.

For `|C|=3`, writing `H=2J` gives a nonsingular Sylvester equation with a unique rational `J`; integrality and Cramer image-lattice tests are exact calibration filters. These fixed-size layers are now intentionally capped: they are not the main proof spine.

## Exact finite calibration

Over the 4,554 alphabet-3 PIP substitutions with image lengths `<=3`:

- all BPA builds terminate below the cap;
- each has one noncoincident sink SCC and every such sink is productive;
- 385,926 reachable noncoincident states occur;
- 385,902 have first defect degree 2;
- 24 have first defect degree 3;
- none has first defect degree `>=4`;
- all 24 degree-3 occurrences are noncentralizer and leak to coincidence within at most two inflations;
- among the 546 substitutions surviving the three-state parity + endpoint + trace filters, none realizes an actual recurrent or sink SCC of size 3; the minimum observed size is 4.

This is evidence only.

## Active next theorem — uniform return/alignment

The next proof obligation must be uniform in `|C|`.

### Prefix-difference route

For a balanced state `T=(u,v)`, define

```text
D_T(k)=Parikh(u[:k])-Parikh(v[:k]).
```

Irreducibility means no interior zero. Under substitution the ordered images expand this to a piecewise lattice walk. Zero returns are exactly balanced child boundaries. In a finite closed SCC, child-state lengths are bounded while total substituted length grows like `beta^n`, so iterates contain a linearly growing number of bounded-gap returns. The target is to couple this return density to contraction in the stable Pisot directions.

### Recognizability route

In the gauge-trivial orientation case, the SCC yields two Parikh-equal word morphisms intertwining the same derived substitution with `sigma`. The missing theorem is an alignment statement: recurrent balanced-child cuts must eventually align with `sigma`-supertile boundaries, or else recognizability is contradicted. This is where the proved unique hierarchy should finally enter Level 3.

## Retired or demoted routes

- predecessor contraction for G1: false;
- displacement/cycle exclusion: false target;
- Mossé desubstitution alone: can remain in the same SCC;
- pure algebra on `N_C`: synthetic solutions exist;
- universal recurrent-SCC synchronization: unnecessary;
- fixed-endpoint `K2` cone: false;
- indefinite `|C|=3` sieve refinement: calibration only unless paired with a uniform completeness theorem.
