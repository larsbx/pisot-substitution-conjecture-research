# Uniform internal coincidence along one minus class-A boundary seed lineage

**Status:** new scoped constructive occurrence-level path, not universal BH. Stacked on [PR #352](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/352) (complete U child carrier and a genuine four-cycle negative control) and its predecessor [PR #349](https://github.com/larsbx/pisot-substitution-conjecture-research/pull/349) (T_m outgoing stars). No claim-governance promotion or independent human review. Existing literature stop/go is [the boundary child-carrier note](class-a-boundary-child-carrier-2026-10-26.md); this continuation imports no new results.

## Work shown

### Assumptions and hypotheses

For **minus** class A only: (k,t\ge0), (n=k+3+t), (d=2n-1-k), (\varepsilon=-1). The literal substitution is (x\mapsto xy^{n+d}x), (c\mapsto cy^nx), (y\mapsto xy^{n-1}c). Let (\beta\in(n+2,n+3)) be the positive Perron root, (u=d/(\beta-1)in(1,2)), (L_y>0), (L_c/L_y=b=1+1/\beta), (L_x/L_y=a=b+u). These facts have exact symbolic certificate provenance in PRs #346–#348. They do not assume global unimodularity, independent physical lengths, arbitrary tile realizability, or a finite balanced-pair closure.

### Derivation / reduction

**Exact four real ordered child occurrences from the aligned root** (each parent is the actual child of the previous step):

| Step | Parent typed offset (top,bottom,x,c,y) | Actual ordinal pair (top,bottom) | Child typed offset |
|---|---|---|---|
| 1 | (S=(x,c,0,0,0)) | ((1,2)) | (T_1=(y,y,-1,1,1)) |
| 2 | (T_1) | ((0,t+1)) | (U=(x,y,1,2,-3)) |
| 3 | (U) | ((d+3,0)) | (V=(y,x,0,-1,1)) |
| 4 | (V) | ((1,2)) | (W=(y,y,0,0,0)) |

The canonical `psc.class_a_boundary_occurrences.symbolic_child` recomputes every proper-prefix Parikh vector and checks (w'=Mw+P_{\rm bottom}-P_{\rm top}) **coefficientwise in (\mathbb Q[t,k])**; actual word bounds are (n\ge3), (1\le t+1\le n-1), (d+3\le n+d), and final run indices (1\le 1\le n-1), (1\le2\le n+d). Therefore no formal six-state or quotient edge is substituted for a word occurrence.

**Strict real overlap at each step.** Write physical offsets in units of (L_y). S has shift 0; (T_1) has (1-u\in(-1,0)), strictly overlapping equal-length y tiles. (U) has shift (u+3/\beta), which intersects x/y strictly since (a-(u+3/\beta)=1-2/\beta>0). (V) has shift (1-b=-1/\beta), so its y/x interiors intersect. W is an actual y/y coincidence, not just equal letters or a zero prefix residual in a disjoint pair. These comparisons require only the established Perron root bound and (1<u<2).

**The final coincidence starts strictly inside the inflated parent overlap.** At the last step, the top y-image is (xy^{n-1}c); its first y starts at (L_x=aL_y>0). The bottom x-image is (xy^{n+d}x), translated by (\beta(L_y-L_c)=-L_y); its second y starts at (-L_y+L_x+L_y=L_x). Hence the true child starting displacement is **zero**, and both y tiles share the physical interval ([L_x,L_x+L_y]). The inflated parent's left overlap boundary is 0 and its top right boundary is (\beta L_y=L_x+(n-1)L_y+L_c). Therefore
[
0<L_x,\qquad L_x+L_y<\beta L_y
]
by (n\ge3) and (L_c>0); the bottom parent extends beyond this common interval. This is a localized internal coincidence event, not an outer-boundary target.

**Result and quantifier.** The selected seed overlap (S) has a literal, four-step occurrence-indexed *existential* path to an internal zero-offset equal-letter child for every (k,t\ge0) in the minus class-A boundary-ray chamber. The particular real state U has such a path of length two. This result does **not** say every seed state, cyclic zipper, SCC, or normalized balanced-pair packet hits; it does not yield finite BPA or G1.

### Evidence and replay

Canonical Mojo: `kernel/psc/class_a_boundary_U_hit.mojo` (symbolic four-step certificate and explicit member path), with `kernel/tests/test_class_a_boundary_U_hit.mojo` replaying full literal image words, all four member-transport Parikh vectors and exact Perron-field overlaps at 24 parameter cells. It also checks that the last common start and y tile end lie **strictly inside** the inflated V top interval. Driver: `kernel/class_a_boundary_U_hit.mojo`. Independent Python `oracles/python/class_a_boundary_U_hit.py` and `tests/test_class_a_boundary_U_hit.py` replay 60 distinct parameters with Fraction-based root enclosures and the correct actual ordered addresses.

From repository root:
```sh
python -m pytest -q tests/test_class_a_boundary_U_hit.py
```
From `kernel/`:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_U_hit.mojo
pixi run --locked mojo run -I . class_a_boundary_U_hit.mojo
```
Dedicated hosted workflow `.github/workflows/class-a-boundary-U-hit.yml` is the exact-revision compilation and runtime acceptance gate. It also reruns PR #352's complete U-carrier test to ensure the new selected path agrees with the complete U outgoing star.

### Negative controls

A same-letter y/y pair chosen at the **bottom first** y ((V\to(1,1))) has nonzero Parikh displacement, so agreement of letters is not a successful target. The selected ((1,2)) pair is instead an actual strictly internal balanced prefix alignment. Reject absent run indices, negative (k) or (t), changed target Parikh coordinates and failure of either physical strictness inequality. The word witness is *existential*: it must not be promoted to global closure or a proof by predecessor contraction.

### Non-claims / remaining gaps

This path neither proves **target-aware BPA parent-child factorization** nor establishes BH over every cyclic strict-zipper seed-reachable vertex. It handles one constructive seed branch and U, not the other 49 next-generation source labels. It does not discharge the C4 interior/newborn hub-residual word obligation, global G1 extraction/termination, A1′, BH, or the general Pisot Substitution Conjecture. No independent human review is asserted. Next: use this path as a **productive base case** in a genuinely forward-closed typed envelope, with explicit ordered occurrence links from all relevant states. The user-facing completion ledger and claim-governance statuses remain unchanged.


**Concurrent research reconciliation:** PR #352 independently obtained the complete U outgoing star and a true four-cycle, which invalidates any universal *all-edge* strict descent. The present four-step branch is distinct: its third edge picks U run ordinal d+3 (not PR #352's forced V_2 at d+2) and proves an **existential** internal coincidence via V_1=(y,x,0,-1,1). A productive exit and a cycle can coexist; neither alone proves universal BH. Earlier stacked PRs #351/#353 are retained as historical superseded proposals, not duplicate implementations.
