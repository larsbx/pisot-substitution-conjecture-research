# Class-A gap sign checker: step (b)

Status: native implementation and bounded sign certificates validated locally; no new
boundary-hitting theorem or universal ledger promotion.
Base: main `d2c3aa8`, after accepted class-C gap-five PR #328.

## Targeted literature stop/go before implementation

The existing [gap-uniformity investigation](class-a-gap-uniformity-stopgo-2026-10-23.md)
already supplies the finite regime fits. Do not regenerate its datasets.
Its next obligation is exact polynomial sign certification on the positive
parameter box in `(h,u=d*h)`, followed separately by rounding and closure.

Three primary sources inspected on October 23:

- Muñoz–Narkawicz, *Formalization of Bernstein Polynomials and Applications
  to Global Optimization*, [author manuscript](https://shemesh.larc.nasa.gov/fm/papers/jar-mn-2012-draft.pdf), §§2.2–2.5: tensor coefficients bound polynomial ranges;
  exact subdivision sharpens them. Bounded search is not complete, and zeros
  on a closed boundary must not be treated as strict positivity.
- NASA [PVS Bernstein library](https://github.com/nasa/pvslib/blob/master/Bernstein/README.md): a machine-checked multivariate implementation and inequality strategies
  already exist. They validate the standard construction, not this Mojo port.
- INRIA [SYNAPS multivariate subdivision documentation](https://www-sop.inria.fr/galaad/software/synaps/MSubdivision.html): tensor-product Bernstein coefficients and de Casteljau subdivision;
  numeric implementations need rounding control. Here every operation is Q.
  MIT's [Bernstein basis exposition](https://web.mit.edu/hyperbook/Patrikalakis-Maekawa-Cho/node9.html) supplies nonnegativity and partition of unity.

Decision: proceed with the standard exact construction, with no novelty
claim for Bernstein positivity. Reuse `psc.param_poly.QX` (row j is u^j,
column i is h^i) and vendored unbounded Q; add neither a rational type nor a
second polynomial algebra. Keep implementation in the PSC sign-decision
layer, alongside its existing specialized univariate Bernstein certificate.

## Contract and strict boundary discipline

Input is a QX polynomial and positive rational H,U. Acceptance establishes
`p(h,u)>0` on `0<h<=H, 0<u<=U`. Remove only the greatest common monomial
`h^a*u^b` with nonnegative exponents; it is strictly positive on this domain.
Scale the residual by h=H*x, u=U*y. Every accepted leaf must have **all**
Bernstein coefficients strictly positive on its closed unit square. Dyadic
de Casteljau splits cover both halves including their shared boundary.
The root leaf may be accepted without subdivision.

No rule of the form 'all coefficients nonnegative, at least one positive'
is used for a closed box: h*(1-h/H) is a counter-control at h=H. Removing a
common lower-axis factor is safe, but h+u still vanishes at the residual
closed origin; a bounded checker may refuse it despite positivity on the
original positive box. Refusal is an undecided certificate, not a negative
witness. The zero polynomial, rejected rationals, nonpositive box bounds,
degree >8, and invalid/exhausted depth or cell budgets must refuse.

For bidegree (m,n), normalized power coefficients a[k,l] give
`b[i,j] = sum_{k<=i,l<=j} a[k,l] C(i,k)/C(m,k) C(j,l)/C(n,l)`.
Two separable passes avoid a dense basis-change matrix. The arithmetic
identity and partition of unity prove the coefficient bound; iterated
closed-box covers prove soundness of finite acceptance. This is a written
standard proof, not a new Lean or PVS formalization.

## PSC calibration target

The existing elimination identity has residual
`R_eps(h,u)=1-eps*h-(1-eps)*h^2-u*h-u*h^2`.
For l>=5,d>=5, the inherited root enclosure gives H=1/25, U=1/5.
Test positivity of R and all three scaled tile lengths
`1+u+(1-eps)*h+u*h`, `1+(1-eps)*h`, `1+h` for both signs.
These are foundational margin calibrations; they do not establish any
carrier's realness, all-child closure, rounding rule or descending rank.

## Evidence and remaining work

Local replay passes the native sign contract and all eight PSC calibrations.
The positive bowl `(h-1/2)^2+(u-1/2)^2+1/16` requires two subdivision levels,
four accepted leaves and seven visited cells. Smaller depth/cell budgets
refuse. Controls also reject an interior zero, a hidden negative interval,
a retained upper-endpoint zero, a zero polynomial, rejected rational input,
nonpositive bounds and degree-budget overflow. The positive `h+u` example
refuses conservatively at the closed residual origin; no negative claim is
made about it. A positive-axis monomial `h^2*u` succeeds after factoring.

An independent Python Fraction oracle agrees with all 225 native Bernstein
coefficients from 25 bidegrees 0..4, and checks equality to the original
polynomial at 225 unisolvent tensor nodes. It audits all 81 bilinear inputs
with coefficients in {-1,0,1}: any accepted decision must satisfy the exact
positive-box corner criterion. Receipt corruption controls reject an altered
coefficient, an omitted coefficient, a duplicate and a false-positive
bilinear acceptance. Those are differential checks, not a formal proof of
this implementation.

The written soundness argument is finite and algebraic: Bernstein weights
are nonnegative and sum to one on a closed box, so positive coefficients
give a positive value. De Casteljau gives the same polynomial on each of
two closed halves, whose union covers their parent. Induction over the
completed finite cover proves positivity of the residual. Multiplication
by the factored positive-axis monomial preserves it on the intended domain.
Budget exhaustion never returns a partial accepted cover.

The packet `evidence/class-a-gap-sign-2026-10-23/` preserves exact native,
independent-oracle and local validation receipts, source hashes and replay
commands. Runtime is the existing minimal lock-matched Mojo compiler; full
locked Pixi provisioning and hosted acceptance remain separate. The new
workflow replays on every `kernel/**` change, following the repaired #328
scheduling contract. No vendored file is changed. Next: derive every
regime's actual margins and rounding obligations; only then connect this
checker to closure/descent. Whole-line A gap five, universal boundary
hitting, G1 and PSC remain open. Independent human review remains pending.
