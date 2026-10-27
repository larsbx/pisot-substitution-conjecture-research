# Independent executable and mathematical audit of #335 (2026-10-23)

Audited submission: `f1ce331bf051385acf8589d88088cbc2271d1350`.
During this audit #335 merged externally at `f5241334a8e5c5fcd91f0033d2592b9e122dee50`;
this correction was published as #340 and merged externally at
`4fe69b636d9092b36758b4f2b42e76dc6b7eaa44` before its hosted checks
completed. This follow-up records the stronger counterexample and fresh
receipts. No human review is asserted.

## Mathematical scope and checks

- **Quadrant positivity:** the four-term expansion at `(l0,d0)` proves the
  sufficient direction on the entire integer quadrant, and the limiting
  slopes prove necessity. Affine residue dependence reduces to endpoints.
  Finite-grid comparisons are regression controls, not the universal proof.
- **Rounding:** the unit-interval cases in Lemma 2 have the correct strict
  and weak endpoints. Lemma 2' lower-ceiling and upper-floor bounds enlarge
  the feasible index range; they cannot discard a realizable child.
- **Perron signs:** the positive root bound gives `u<1/l0` and `0<t<=1/d0`.
  Bernstein coefficients bound the polynomial on each closed cell. The
  governing coefficients cover every included sub-face, including the
  closed top edge. Hull skipping requires every side coefficient strictly
  negative. The hull-multiple fallback uses the sign of its multiplier in
  the correct direction and only strips positive monomial factors.
- **Closure:** the child difference range of the two contiguous occurrence
  runs is an integer interval. Uniform rounding and clipping examine a
  superset. Interval ordering is checked for every `l>=l0`; uncovered gaps
  require one uniform geometric exclusion margin, including both residue
  endpoints, rather than mixing margins across endpoints. Displacement is
  increasing in the parent index, since `d h(1+h)>0`. Outside the finite
  child-y window it is increasing with increment `L_c+eps h=1+h>0`.
- **Descent:** pieces and subpieces must partition their row intervals.
  Child type, shifted piece containment, realizable occurrence differences,
  strict overlap and an integer potential drop of at least one are checked
  at interval endpoints. The potential is nonnegative for every `l>=l0`.
  Its zero-offset targets establish boundary hitting, not a new universal
  coincidence or PSC assertion.
- **Assembly:** low/middle/high intervals cover all residues from gap 7
  (minus) and 11 (plus). Registered uniform floors can exceed fitted floors;
  the intervening rays are re-certified, and their finite lower prefixes
  use complete cap-refusing graphs. The seven exceptional plus rays are
  separate ray certificates, with the extra `n=37` graph for `(d,r)=(7,2)`.

The universal quantifiers enter through these polynomial/affine certificates;
no fitted graph window supplies a missing quantifier. The archived SHA256
manifest passes unchanged. This review found no mathematical refutation of
the scoped family in the inspected arguments; executable acceptance remains
separate and requires the dedicated hosted job below.

## Defects corrected

1. **Generic box-denominator overflow:** `53^11` overflows signed Int64.
   Before the correction, `box_polynomial(1+h^11,1,53)[11][11]` has sign -1,
   although its exact value is `1/53^11>0`. Worse, the original verifier
   certifies `(1-53h)^2-h^11` as positive at `(l0,d0)=(1,53)`, while exact
   evaluation at `u=999999999999/1000000000000`, `t=1/53` (hence
   `h=999999999999/53000000000000`) is negative. This interior point obeys
   every box constraint. The corrected verifier refuses the sign-changing
   polynomial. This violates the generic sign
   verifier's arithmetic contract even with both floors below 64. Reciprocal
   powers now use the existing unbounded `Q` arithmetic; the regression
   checks equality with the exact rational, not only its sign. The submitted
   theorem's low-degree margins are not this counterexample.
2. **Suppressed test assertions:** the polynomial-grid test placed its
   assertion inside the handler for an undecided sign. Assertions now run
   outside that handler, so a disagreement fails the test.
3. **Missing hosted assembly replay:** the existing workflows do not
   explicitly invoke the new uniform-gap tests. A dedicated locked workflow
   now runs gap arithmetic, hull signs, closure, occurrence descent, the
   complete assembly, exceptional rays and zipper controls. Its conservative
   `kernel/**` trigger includes transitive arithmetic and table dependencies.

The executable still accepts floors only in `1..64`. This is a supported
interface range, not a bound on the quantified mathematical `l,d`. A
certificate at floor 5 proves all larger members without representing those
members as machine integers. Nor does monotonicity imply that every
certificate accepting above 64 must accept at 64. The corrected design note
makes this distinction explicit. The scoped assembly uses `l0=5,d0<=11`.

## Evidence and replay

Fresh local checks use the compiler pinned by `kernel/pixi.lock`,
`Mojo 1.1.0.dev2026090805 (34562fa1)`. A pre-existing minimal runtime needs
its own corrected local `MODULAR_HOME` paths; normal `pixi install --locked`
was blocked downloading a conda dependency. This is local tooling evidence,
not a successful locked hosted installation.

- Python ray, parity and integrity suite: 115 collected tests passed.
- Native polynomial/hull regression, including the new overflow control: passed.
- Native gap arithmetic, including floor 64 acceptance and 65 refusal: passed.
- Native regime-descent test: passed, including altered tables and occurrences.
- Native 25-ray suite: passed, including exact prefix graphs, differential
  occurrence replay at two members and damaged-table controls.
- Claim-governance audit and archived manifest: passed.
- Six independent Fraction/Sturm stress rays at `d=1,000,003`, low/high/middle
  of both signs, certify closure and descent for every `l>=64`. These test
  six fixed rays, not uniformity in `d`.
- Full native assembly: passed for both signs, all 18 regimes, four minus
  finite rays, seven plus exceptional rays and three exact prefix graphs.
  The counts reproduce the archived theorem receipts. The scope stays n>=5d.
- Hosted acceptance: still queued at the latest inspection; no completed
  hosted acceptance is inferred from #335 or #340 having merged externally.

Replay with the normal pinned environment, from `kernel/`:

```sh
pixi run --locked mojo run -I . tests/test_poly_hu.mojo
pixi run --locked mojo run -I . tests/test_gap_form.mojo
pixi run --locked mojo run -I . tests/test_class_a_gap_uniform.mojo
pixi run --locked mojo run -I . tests/test_class_a_gap_regime_descent.mojo
pixi run --locked mojo run -I . tests/test_class_a_gap_theorem.mojo
```

From the root:

```sh
python -m pytest tests/test_class_a_residue_rays.py tests/test_class_a_d2_plus_ray_carrier.py tests/test_recorded_data_integrity.py
python oracles/python/class_a_gap_regime_adversarial.py
(cd evidence/class-a-gap-theorem-2026-10-23 && sha256sum -c SHA256SUMS)
```

## Non-claims

The `n<5d` strip remains open. This audit does not close class C, universal
#139/#84, G1 or PSC. It supplies no independent human-review event. Historical
receipts are preserved; fresh CI is required on the corrective revision.

Fresh local receipts and source digests: `evidence/class-a-gap-independent-audit-2026-10-23/`.
