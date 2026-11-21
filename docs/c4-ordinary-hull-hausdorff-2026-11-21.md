# The ordinary tiling hull is Hausdorff

**Status:** Lean proves `T2Space (LocalHull S)` for every length substitution `S`, in the
ordinary small-translation/window topology of the
[ordinary-hull note](c4-ordinary-hull-topology-2026-11-19.md). This closes the
Hausdorff part of that note's gap 1. The instance applies unchanged to the σₖ
[family hull](c4-family-tiling-2026-11-21.md), which is a `LocalHull`. No external input
is used. Compactness is not proved. Independent human review is pending. C4 and PSC remain
open; no governed claim changes.

Starting revision: `main@7de25513`.
[Source decision](c4-ordinary-hull-hausdorff-stop-go-2026-11-21.md).

## Work shown

Module [`PeriodicPartnerLocalHausdorff.lean`](../proof/PscVerif/PscVerif/PeriodicPartnerLocalHausdorff.lean).

| Lean | Statement |
| --- | --- |
| `mem_of_approx` | If a tiling `X` contains `(a, x + r)` for arbitrarily small `|r|`, then `(a, x) ∈ X`. Two such copies at offsets within `ℓ a / 2` of `0` share a point, so tiling uniqueness makes them equal. A nonzero offset would then be undercut by a smaller one. |
| `eq_of_approx` | If `T` agrees on every window with arbitrarily small translates of `U`, then `T = U`. A tile of either tiling has arbitrarily close copies in the other, and `mem_of_approx` applies. |
| `mem_patch_self` | Every basic neighbourhood contains its centre. |
| `approx_of_patches` | If `patch T ε n` meets `patch U ε n` for all `ε > 0` and `n`, the hypothesis of `eq_of_approx` holds. The two witnesses give translations `t`, `s`, and `U` agrees with `T` translated by `s − t` on `(-(n − |s − t|), n − |s − t|)`. |
| `instance : T2Space (LocalHull S)` | Distinct points have disjoint basic neighbourhoods. |

Every compiled declaration uses only `propext`, `Classical.choice` and `Quot.sound`.

## Replay

```sh
./tools/check_c4_periodic_partner.sh
python3 tools/make_proof_bank.py --check
```

## Non-claims / remaining gaps

1. **Compactness of `LocalHull` is not proved.** It needs finite local complexity and a
   legality-preserving diagonal limit. A metric for the ordinary topology is not
   constructed either.
2. Recognizability, the concrete maximal equicontinuous factor, its finite fibres and the
   map identifications in the roadmap's family factor-geometry row are unchanged.
3. Realization continuity (#627) and the finite-to-one σₖ realization (#643) are the
   subjects of open PRs.
