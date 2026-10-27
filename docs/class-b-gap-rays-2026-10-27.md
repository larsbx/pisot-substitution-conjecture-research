# Class B's top layer: per-gap ray certificates for plus g = 6..10 and minus g = 4..7 (2026-10-27)

**Status:** repository-proved, computer-assisted, scoped to nine more lines of
class B's top layer, each on its whole PIP domain:

- plus, `(p, q, r) = (3q + 12 − g, q, q + 1)`, `g = 6, …, 10`;
- minus, `(p, q, r) = (3q − g, q, q − 1)`, `g = 4, …, 7`.

Independent human review is pending. Together with
[step 2](class-b-ray-certificate-2026-10-27.md) (plus `g ≤ 5`, minus `g ≤ 3`)
the certified lines are now plus `g ≤ 10` and minus `g ≤ 7`. No ledger claim is
promoted; the status is that of the executable certificate.

This is item 3 of the decision in the
[step-2b stop/go](class-b-gap-uniformity-stopgo-2026-10-27.md): the gaps below
the regime floors are ray-by-ray work. It shrinks that leftover set to plus
`g = 11..15` and minus `g = 8..11`.

## Method

Nothing new is proved here: the 62 rays go through step 2's certificate
unchanged (Theorems A_B and B_B and Corollary L_B of
[class-b-ray-certificate-2026-10-27.md](class-b-ray-certificate-2026-10-27.md)),
which is generic in `g ≤ 16`. Only the inputs are new.

- **Carriers.** Each ray `(eps, g, r)` is fitted from exact native label sets
  (`kernel/class_b_label_rays.mojo`, now allowed `g ≤ 16`, `q ≤ 128`) as in
  step 1: the earliest floor whose first two members predict every later
  member. `oracles/python/class_b_gap_rays.py` refuses a fit checked on fewer
  than two further members; here each is checked on 4–8.
- **Potentials.** `oracles/python/class_b_ray_tables.py`, as in step 2: the
  least fixed point of the descent inequality on two graphs of the ray.
- **Certified floors.** 27 rays certify at their fitted floor. 35 refuse there
  (19 `UNDECIDED` affine maxima or minima, 16 `NO DESCENT`) and certify with the
  floor raised by `g`, two of them (minus `g = 5, 6`, `r = 1`) by `2g`. The
  carrier intercepts are absolute in `l`, so raising a floor changes no row; the
  members below it become exact graphs. The raised floor is stored as
  `certify_floor` in the packet, exactly as step 2's `FLOORS` raised minus
  `g = 3`.

## Results

| branch | `g` | fitted floors, `r = 0, 1, …` | certified floors | rows | `max b` |
| --- | ---: | --- | --- | --- | ---: |
| plus | 6 | 18, 25, 20, 21, 22, 23 | 18, 25, 20, 21, 22, 23 | 235–267 | 3 |
| plus | 7 | 21, 22, 23, 24, 25, 26, 27 | 28, 22, 30, 24, 25, 26, 27 | 221–257 | 3 |
| plus | 8 | 24, 25, 26, 27, 28, 29, 30, 31 | 32, 33, 26, 35, 28, 29, 30, 31 | 206–244 | 3 |
| plus | 9 | 27, 28, 29, 30, 31, 32, 33, 34, 26 | 36, 37, 38, 30, 40, 32, 33, 34, 35 | 199–247 | 3 |
| plus | 10 | 30, 31, 32, 33, 34, 35, 36, 37, 38, 29 | 40, 41, 42, 43, 34, 45, 36, 37, 38, 39 | 188–238 | 3 |
| minus | 4 | 20, 21, 18, 19 | 24, 25, 22, 23 | 212–232 | 4 |
| minus | 5 | 25, 21, 22, 23, 24 | 30, 31, 27, 28, 29 | 196–220 | 4 |
| minus | 6 | 30, 25, 26, 27, 28, 29 | 36, 37, 32, 33, 34, 35 | 194–216 | 3 |
| minus | 7 | 28, 29, 30, 24, 32, 26, 34 | 35, 36, 30, 31, 32, 33, 34 | 180–206 | 3 |

Common to every new ray: 9 real seeds, 3 non-strict seed candidates, 8 target
pieces, 86 terminal splits, 0 clip fallbacks, and 112 new labels per `l`-step.

**Corollary (nine more lines).** On each line above, every vertex reachable
from the three swap seeds has an offset-zero descendant, for every PIP member:
members at or above the certified floor by Theorems A_B and B_B on their ray,
and members below it by exact uncapped complete graphs (mode `below`). The
consequences follow as for Corollary L_B.

## Work shown

### Assumptions and hypotheses

The nine lines above with `q = g l + r`, the open top layer as checked by
`BRay.check_domain`, and step 2's objects (canonical swap seeds, proper-prefix
occurrences, bottom-minus-top integral offsets, equal-letter offset-zero
terminals). No hypothesis is added.

### Derivation / reduction

Step 2's Lemmas 1–4 and Theorems A_B, B_B apply verbatim: the closed forms
`L` and `T = (β+1)(uβ − eps d) − gβk` and the elimination `qβ(β+1) = A(β)` hold
for every `g`. Each check reduces to integer polynomial signs on
`(0, 1/β_low]` and affine comparisons on `l ≥ l0`.

### Evidence and replay

From `kernel/`:

```bash
pixi run --locked mojo run -I . -I tests tests/test_class_b_ray_certificate.mojo
pixi run --locked mojo build -I . class_b_ray_certificate.mojo -o build/class-b-ray-certificate
build/class-b-ray-certificate all          # 83 rays
```

From the repository root:

```bash
python oracles/python/class_b_ray_certificate.py
python oracles/python/class_b_ray_tables.py --check
python oracles/python/class_b_gap_rays.py evidence/class-b-gap-rays-2026-10-27/labels plus:6-10 minus:4-7 --out /tmp/refit.json
(cd evidence/class-b-gap-rays-2026-10-27 && sha256sum -c SHA256SUMS)
```

The packet [`evidence/class-b-gap-rays-2026-10-27/`](../evidence/class-b-gap-rays-2026-10-27/)
holds the 544 native label sets, the fit log, the per-ray native certificate,
replay and below-floor log of all 83 rays, the oracle log, and both count
streams.

- **Both verifiers.** The Mojo certificate and the independent Python verifier
  report identical counts on all 83 rays (`diff native.counts oracle.counts`
  is empty).
- **Replays.** At the certified floor and one period above it, each native
  graph equals the carrier and every native vertex has a native edge that
  lowers `X` (166 replays).
- **Below the floors.** Every PIP member below a certified floor is an exact
  graph that hits (83 checks).
- **Refit.** The fitter reproduces `carriers.json` from the archived labels
  exactly, except for the `certify_floor` fields.
- **CI.** `.github/workflows/class-b-ray-certificate.yml` reruns `all`, now
  expecting 83 rays, and diffs the two count streams. The Mojo test certifies
  every tabulated ray.

### Negative controls

Step 2's controls run unchanged in the same test and pytest: a removed row,
a lowered, zero or missing potential, another ray's carrier and sub-floor
certificates all refuse. The 35 refusals at the fitted floors (19 `UNDECIDED`,
16 `NO DESCENT`) are refusals of the certificate itself, recorded here and in
the commit history rather than hidden.

### Non-claims / remaining gaps

- **Lines.** Plus `g ≥ 11` and minus `g ≥ 8` remain open. The step-2b regime
  route covers plus `g ≥ 16` and minus `g ≥ 12` only as a floating-point
  profile, so plus `g = 11..15` and minus `g = 8..11` still need ray
  certificates, and the regime certificate itself is not built.
- **Open.** Universal BH, A1′, #84, G1 and PSC remain open.
- **Not formalized.** Nothing here is Lean-formalized, and independent human
  review is pending.
