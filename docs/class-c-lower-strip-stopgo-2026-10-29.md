# Class C lower strip: stop/go, 2026-10-29

Target: certify parameter pieces below T_C without assuming PIP or a constant
label set. Reproduce #384 at source 53dd9547cea65d3cdb1fa80c4e16f97b712aabd4
first. Keep the two below-onset controls (198/216 versus 196/214).

## Targeted primary-source check

Inspected 2026-10-29:

- Akiyama–Lee, *Algorithm for determining pure pointedness of self-affine
  tilings*, Adv. Math. 226 (2011), 2855–2883,
  https://arxiv.org/abs/1003.2898. Finite overlap graph closure and coincidence
  are the closest construction. Their all-overlap/Meyer hypotheses do not
  identify a canonical swap-seed graph with all legal overlaps.
- Sellami, *Balanced pair algorithm for a class of cubic substitutions*,
  Turk. J. Math. 39 (2015), 91–102, DOI 10.3906/mat-1407-3,
  https://journals.tubitak.gov.tr/math/vol39/iss1/9/.
  Uniform parametric balanced-pair computations are prior art. That paper's
  unimodular beta substitutions do not include these determinant ±2 matrices.
- Akiyama, *Strong coincidence and overlap coincidence*, DCDS 36 (2016),
  5223–5230, DOI 10.3934/dcds.2016027,
  https://www.aimsciences.org/article/doi/10.3934/dcds.2016027.
  The many-control-point coincidence hypothesis is stronger than one
  swap-seed boundary-hitting computation. No spectral consequence is imported.

These sources and the existing S′ cone argument support using the existing
certificate shape, not claiming a new coincidence criterion or full PSC.
The unchanged non-unit and realization firewalls remain in force.

## Proposed reduction and controls

For M=[[2,1,0],[0,1,2],[n+d,n,n-d+eps]], derive
chi=t^3-(n-d+eps+3)t^2+(n-3d+3eps+2)t-2eps.
The identities chi(1)=-2d, chi(2)=-2(n+d), and
chi(-1)=-2(n-2d+3eps+3) suggest a direct exact proof of the
PIP-domain boundary, independent of the cone engine's sufficient Rouché test.
Check this before stating the previously observed starts as a theorem.

Explore fixed n-4d diagonals and fixed-d gap lines. For a two-dimensional
candidate use d=a+b+u+v, n=4a+3b+4u+3v, u,v>=0. This is exactly
3d+a<=n<=4d-b, with inverse u=n-3d-a, v=4d-b-n; its lattice determinant is -1.
Do not combine pieces using a required common label set. Check exact closure
and hitting first; record constant labels only when independently established.

Negative controls: the two adjacent diagonals have different labels; the
Pisot boundary has chi(-1)=0 one integer below each proposed start; gap 6's
onset line refuses a varying intermediate sign despite true memberwise BH.
An undecided sign is not a counterexample. A cap is not a verdict.

Decision: **proceed with narrowed targets**: exact PIP-domain inequalities,
separately certified diagonals, and a conservative middle-strip cone if the
unchanged engine decides it. No all-strip, PDS, G1 or PSC promotion. Preserve
all failed candidate partitions and their exact refusal reasons.
