# Hausdorffness of the ordinary hull: source decision

**Status:** Source decision for the Hausdorff part of gap 1 of the
[ordinary-hull note](c4-ordinary-hull-topology-2026-11-19.md). The
[roadmap](research-roadmap-2026-09-21.md) lists it among the family factor-geometry
premises: "prove the ordinary-hull compactness, Hausdorffness and map-identification
premises required by the chosen imports". Starting revision: `main@7de25513`. No governed
claim changes.

## Exact target

`T2Space (LocalHull S)` for every `LengthSubst S`, in the topology already defined on main,
the open quotient of `ℝ × Hull` by translation. Its neighbourhood basis
`patch S T ε n` was proved there: a translation smaller than `ε` followed by agreement
on `(-n, n)`.

## Sources

| Source | Use and boundary |
| --- | --- |
| Anderson–Putnam (1998), *Topological invariants for substitution tilings and their associated C\*-algebras*, ETDS 18, §2 | The tiling metric is a metric; its Hausdorffness is standard. Bibliographic only, **not re-opened**. Nothing is imported. |
| Sadun, *Topology of Tiling Spaces* (AMS ULS 46, 2008), ch. 1 | Same, for the small-translation/window topology. Bibliographic only, **not re-opened**. |

## Transfer

- The standard proof uses only that a tiling has one tile through each point and that tiles
  have positive length. Both are fields or definitions of the hull. Finite local
  complexity, compactness and recognizability are not needed.
- Meeting basic neighbourhoods must be turned into agreement with an arbitrarily small
  translate on arbitrarily large windows. This uses only the existing agreement-shift and
  transitivity lemmas.

## Decision

**Proceed** with Hausdorffness alone. **Defer** compactness. It needs finite local
complexity of the legal patches and a diagonal limit argument that keeps legality, and it
is a separate increment.
