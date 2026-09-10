# Conjecture ledger

The machine-checked dependency form is `tla/Ledger.tla`. This prose ledger distinguishes three statuses deliberately:

- **proved unconditionally**;
- **proved conditional on a given finite closed nonproductive SCC (FCS)**;
- **open global conjectures**, including G1 and C1–C4.

## G1 — finiteness of the repository balanced-pair automaton

**Statement.** For every primitive irreducible Pisot substitution on a 3-letter alphabet, the repository graph `B_sigma` is finite.

**Status.** Open in the current repository. The predecessor-contraction proof of `PSC_PROOF_v5` Theorem 5.1 is withdrawn: `beta * L(s') <= L(s) + D` is false, with observed worst ratio 8.0 and unbounded excess.

**Literature alignment.** The standard balanced-pair literature gives, for irreducible Pisot substitutions, pure discrete spectrum iff the balanced-pair algorithm terminates with coincidence and notes a seed `(ij,ji)` criterion. This strongly bears on G1, but the repository will not silently identify the literature algorithm with its normalized all-seed graph. `docs/bpa-literature-bridge.md` records the exact closure/reachability bridge still required before promoting `PDS => G1` into the machine ledger.

**Evidence, not proof.** The exact alphabet-3, image-length-`<=3` corpus has 4,554 PIP substitutions; all 4,554 BPA constructions terminate below the cap.

## C1 — SCC Producer

**Statement.** Every recurrent noncoincident SCC of `B_sigma` is productive: some path reaches a coincidence.

**Status.** Open in general.

**Finite-BPA reduction.** Let `NP` be the set of nonproductive states. `NP` is forward-closed. If the BPA is finite and `NP` is nonempty, the condensation of the induced graph on `NP` contains a sink SCC, and that SCC is closed, recurrent, noncoincident, and nonproductive. Thus under G1 it suffices to rule out strict closed/sink nonproductive SCCs. See `docs/sink-scc-reduction.md`.

This does **not** require synchronization on every recurrent SCC. Escaping recurrent SCCs may fail local boundary tests and later become productive.

## C2 — sink-SCC boundary escape

**Statement.** Every strict closed nonproductive recurrent noncoincident SCC has a zero-return boundary at some inflation whose right adjacent pair lies in `Sync_+` or whose left adjacent pair lies in `Sync_-`.

**Status.** Open.

By the Boundary Synchronization Lemma, such a boundary contradicts nonproductivity. Under G1 plus the sink-SCC reduction, C2 is sufficient for C1.

## C3-local — one-step newborn escape

**Statement.** Every strict closed nonproductive recurrent noncoincident PIP SCC contains a state `T` such that `sigma(T)` has an interior zero-return cut with a synchronizing adjacent endpoint pair.

**Status.** Open, but the horizon/locality reduction is proved.

`docs/c3-locality-reduction.md` proves that a higher-inflation newborn synchronizing cut localizes to a one-step newborn cut of an irreducible state in the same closed SCC. Hence arbitrary inflation depth is no longer the load-bearing difficulty.

**Exact finite evidence.** In the 4,554-PIP corpus, all 60 recurrent SCCs that fail the one-step inherited/newborn synchronization test are singleton SCCs with noncoincident exits; none is a closed counterexample candidate.

## C4 — eliminate the nonsynchronizing strict component

**Statement.** No strict closed nonproductive recurrent noncoincident PIP SCC can keep every one-step interior newborn boundary trapped in the nonsynchronizing endpoint cores.

**Status.** **Active main theorem target.** C4 is sufficient for C3-local; the current one-way proof route is

```text
C4 => C3-local => C2 => C1,
```

with G1 used to extract the finite sink obstruction from global nonproductivity.

### Proved C4 reduction stack

The following are theorem-grade reductions or exact identities; none by itself proves C4.

1. **Endpoint synchronization quotient.** The 27 self-maps on three letters have seven conjugacy types A–G. A/B are globally synchronizing. Eventual endpoint synchronization is an equivalence relation and the endpoint map induces a permutation on its quotient.
2. **Global endpoint eliminator.** If either `sigma_+` or `sigma_-` is globally synchronizing, every balanced pair is productive. This is unconditional: no Pisot or G1 assumption is needed.
3. **Endpoint-signature reduction.** In a hypothetical strict SCC the projected endpoint regime has at most 1, 3, or 9 signatures depending on quotient sizes.
4. **Parikh intertwiner.** For an FCS, `P_C N_C = M_sigma P_C`. Irreducibility of `chi_M` forces `rank P_C=3`, hence `|C|>=3`, `chi_M | chi_N`, and `rho(N_C)=beta`.
5. **Orientation cocycle.** Normalization `(u,v)~(v,u)` hides a `Z/2` child-orientation cocycle. With positive/negative occurrence matrices `A,B`, `N=A+B` and `S=A-B`; the oriented double cover splits into even `N` and odd `S`, with `rho(S)<=beta`.
6. **Signed first-defect intertwiners.** At the first nonzero scattered-subword defect degree, the normalized component carries a signed representation quotient. In particular `Q2 S=(Lambda^2 M)Q2`; when `K2=0`, `Q3 S=Phi3 Q3`.
7. **Degree 3.** A strict closed `K2=0` component must have its `K3` image in the two-dimensional determinant/centralizer eigenspace.
8. **Degree 4 / higher.** The free-Lie degree-4 floor and generalized-Witt mod-3 sieve reduce possible low-growth higher defects to near-balanced weight families.
9. **Degree-2 parity size sieve.** Since `N congruent S (mod 2)`, a degree-2 counterexample has an SCC-size lower bound in `{3,4,5,6}` determined by the mod-2 lcm of the characteristic cubics of `M` and `Lambda^2 M`.
10. **Ordered degree-2 factorization identity.** The mid-area equation

   ```text
   (Lambda^2 M) H + 2 C_sigma P = H N + 2 Omega_tau
   ```

   retains ordered child-factorization information that the signed `K2` intertwiner discards.
11. **Three-state calibration only.** When `|C|=3`, the mean-area Sylvester equation has a unique rational solution; integrality and Cramer-image tests provide exact negative-template filters. These are intentionally **not** the continuing main proof strategy.

### Exact finite calibration

For the established 4,554 PIP substitutions with image lengths `<=3`:

- all BPA builds terminate below the cap;
- each substitution has exactly one noncoincident sink SCC;
- every such sink has a direct coincidence child and a newborn synchronizing boundary;
- 385,926 reachable noncoincident states occur;
- 385,902 have first defect degree 2;
- 24 have first defect degree 3;
- none has first defect degree `>=4`;
- the 24 degree-3 occurrences are noncentralizer and leak to coincidence within at most two inflations;
- among 546 substitutions surviving the three-state parity + endpoint + trace diagnostics, none has an actual recurrent or sink SCC of size 3; minimum observed size is 4.

All of this is finite evidence, not a proof of C4 or G1.

## Active uniform proof target

The next main argument must be uniform in `|C|`. Two theorem-grade ingredients are underused:

1. **Prefix-difference return structure.** For `T=(u,v)`, `D_T(k)=Parikh(u[:k])-Parikh(v[:k])`; zero returns are exactly balanced child boundaries after inflation. A finite closed SCC gives bounded child lengths while substitution length grows like `beta^n`, hence recurrent dense return structure.
2. **Recognizability / supertile alignment.** In the gauge-trivial orientation case the SCC gives two word morphisms intertwining the same derived substitution with `sigma`. The missing step is to force recurrent balanced-child cuts to align with substitution supertile cuts, or derive a contradiction.

The main C4 program should now attack an **alignment-or-return-density lemma**, not add more fixed-size sieves.

## Retired / blocked routes

- predecessor contraction for G1: false;
- displacement/cycle exclusion: false target;
- Mossé desubstitution descent alone: can remain in the same SCC;
- pure algebra on `N_C`: synthetic solutions exist;
- universal synchronization of every recurrent SCC: unnecessary;
- fixed endpoint `K2` half-space/cone: false; explicit same-endpoint vectors positively span the origin;
- indefinite stacking of `|C|=3` sieves: retained only as calibration unless a completeness theorem is supplied.
