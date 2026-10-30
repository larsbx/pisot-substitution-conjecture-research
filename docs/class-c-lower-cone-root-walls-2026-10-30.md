# Class C lower cone: exact Perron-root walls and first boundary-hitting rays (2026-10-30)

**Status:** exact hand-proved algebraic inequalities at the stated class-C PIP scope, awaiting independent mathematical review. The proposed symbolic BH ray certificates are *conditional* until their hosted native jobs succeed; no PDS, G1, all-overlap realization, or PSC claim is made.

This note starts **below** the proved T_C2 band of merged PR #399, not in the already closed region. Theorem P_C of merged #397 establishes the exact PIP domain, and merged #400/#401/#402 repair its governance, evidence, and CI workflow issues. The trusted `psc.symbolic_cone` implementation is **unchanged**.

## Work shown

### Assumptions and hypotheses

The class-C substitution is

    x -> x y^(n+d) x,
    c -> c y^n x,
    y -> c y^(n-d+eps) c,   eps = +1 or -1.

Set `d>=7`; these are the gaps with remaining lower-cone BH work. In the **plus** cone write `n=2d-5+c`, and in the **minus** cone write `n=2d+1+c`, with integer `c>=0`. The residual restriction `n<3d` means

    plus: 0 <= c <= d+4;
    minus: 0 <= c <= d-2.

Theorem P_C proves PIP throughout both regions. In particular the Perron root `beta>2` is the *only* root of `chi` outside the open unit disc. All inequalities below are **exact polynomial identities**, not numerical root estimates. Put `r=n-d+eps`.

### Derivation / reduction

The characteristic polynomial has the identity

    chi(t) = (t-r)(t-1)(t-2) - 2n(t-2) - 2(n+d).

For `t>2`, the quadratic factor of `chi(t)/(t-beta)` is positive: its roots lie strictly in the open unit disc. Therefore `sign chi(t)=sign(t-beta)`.

Direct substitution and cancellation yield:

| branch | chi(r+3) | chi(r+4) | chi(r+5) |
|---|---|---|---|
| plus, n=2d-5+c | c(c-1)-d(d-1)-2 | 2(c²+cd-1) | 3c²+4cd+5c+d²+3d |
| minus, n=2d+1+c | c(c+3)-d(d+3)+2 | 2(c²+cd+6c+2d+9) | 3c²+4cd+25c+d²+15d+52 |

All expressions are integers, and the identity is valid even outside the PIP cone; only the interpretation as a unique root comparison uses P_C.

**Exact spectral wall (algebraically proved).** For every integer `d>=7` in the residual lower cone:

1. Plus at the **single PIP edge** `c=0`: `r+4 < beta < r+5`. The lower inequality follows from `chi(r+4)=-2`, the upper from the positive displayed `chi(r+5)`.
2. Plus for `1<=c<=d`, equivalently `2d-4<=n<=3d-5`: `r+3 < beta < r+4`. The upper bound follows from `c²+cd-1>=d>0`; the lower follows from `c(c-1)<=d(d-1)`, hence `chi(r+3)<=-2`.
3. Plus for `d+1<=c<=d+4`, equivalently `3d-4<=n<3d`: `r+2 < beta < r+3`. At `c=d+1`, `chi(r+3)=2d-2>0\); this polynomial increases for integer `c>=0`, so the upper bound persists. `chi(r+2)<0` throughout the PIP domain.
4. Minus for the **whole residual lower cone** `0<=c<=d-2`: `r+3 < beta < r+4`. At `c=d-1`, `chi(r+3)=-2d<0`; its integer forward difference `2c+4>0`, so the lower c values have negative `chi(r+3)`. The displayed `chi(r+4)` is strictly positive.

These open intervals are disjoint spectral regimes on the plus side. In particular, **the rational wall `beta=r+3` is crossed between `n=3d-5` and `n=3d-4` on plus**, whereas minus remains above `r+3` throughout its lower cone. At the plus PIP boundary `beta=r+4` is crossed between `n=2d-5` and `n=2d-4`. Neither wall assumes any overlap-label constancy.

For reference, the universal exact inequality `chi(r+2)<0` follows by direct substitution: on plus `chi(r+2)=-2((d-1)c+d²-3d+3)`; on minus `chi(r+2)=-2((d+1)c+d²+3d+1)`. Both parenthesized quantities are positive for `d>=7,c>=0`. Thus `beta>r+2`; the positive `chi(r+5)` gives `beta<r+5` uniformly. The walls partition the *entire* previously open cone by explicit integer inequalities.

**Proof use.** The wall at `r+3` is precisely an algebraic comparison that can be supplied to parametric overlap run-window sign readers without presuming a frozen graph. A later cone partition should be split along `n=3d-4` on plus and at the exact PIP edge `n=2d-5`, rather than attempting to certify either sign across these transitions.

### Evidence and replay

The canonical integer-identity regression in `kernel/class_c_lower_cone_root_walls.mojo` independently computes `chi` at `r+2`, `r+3`, `r+4` and `r+5` for finite `d,c` and asserts the closed formulas and all four regimes. This is a **bounded test**, not the quantified proof, which is the algebra above. A separate standard-library Python checker `oracles/python/check_class_c_root_walls.py` uses its own polynomial evaluation and also asserts sharp crossing controls. No floating point is used.

The follow-on driver `kernel/class_c_lower_cone_rays.mojo` attempts BH (not frozen labels) on fixed `k=n-3d=-1,-2` rays for both signs. It searches for a certificate from a shifted integer gap `D`, requires uniform symbolic PIP + all-vertex zero reachability, checks all exact vertex keys at `D+1,D+2`, and separately checks every gap `7<=d<D` by the fail-closed exact graph kernel. A sign/affine-fit refusal only shifts the candidate; any graph mismatch, cap, or unproductive vertex aborts. **No success is assumed here.**

Acceptance requires successful hosted workflow jobs in `.github/workflows/class-c-lower-cone-root-walls.yml`. Old T_C, T_C2, and diagonal checks are not weakened.

### Negative controls

- Plus `c=0`: `chi(r+4)=-2` (so any proof of `beta<r+4` for every PIP member is wrong).
- Plus `c=1`: `chi(r+4)=2d>0`; this is the sharp adjacent transition.
- Plus `c=d`: `chi(r+3)=-2`; plus `c=d+1`: `chi(r+3)=2d-2>0`. These rule out a common `r+3` sign over the entire lower cone.
- Minus `c=d-1`: `chi(r+3)=-2d<0`, immediately above the lower cone, while `c=d`: `chi(r+3)=2>0`. Thus extending the minus inequality beyond `n=3d` without splitting fails.
- These are signs of a polynomial at a rationally shifted *algebraic* point; they are not BH counterexamples, and an undecided cone closure must never be treated as one.

### Non-claims / remaining gaps

The spectral walls are **new exact constraints**, not proof of the lower-cone BH property. The four proposed fixed-k rays remain conditional until native jobs actually emit `BH_CERTIFIED`. Even successful rays would leave most of the growing-label lower cone open. Near `n=2d+O(1)`, a finite frozen graph is not plausible: exact profiles show graph growth with gap. A parametric carrier and explicit child/productivity certificate, with edge/recurrent-state families, remains necessary.

Independent human review and independent verification of the implementation of `psc.symbolic_cone` remain outstanding.
