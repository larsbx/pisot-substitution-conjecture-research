# Typed cross-strip fan-in evidence

Parent: #436 at 3ee6f9bcbc075822cc1800b4f2ab979dbe2cf2f5.
This extension is stacked separately on that branch. Earlier graph, ladder,
transfer-plane and signed-strip evidence packets are preserved unchanged.

The [written proof](../../docs/class-a-x-cross-strip-2026-10-31.md)
specializes typed RUN shear covariance to Z(p,s,1)=(x,y,p,3p+s,1-s-6p).
For k,t>=0, K=k+1,n=k+t+3,D=floor((n-1)/K), it proves:

* p>=0,Kp<=n-1,-3<=s<=3: exactly 2p+2 selected edges to typed C.
* p<0,K(-p)<=t,-3<=s<=1: at most 4D+6 selected edges to typed C.
* Both genuine orientations, with full negated offsets and swapped indices.

These are sufficient local sectors, not maximal guarded domains or a
forward-closed carrier covering X descendants. No universal BH, spectral
bridge or complete Pisot substitution proof is claimed.

## Executed receipts

* `native-cross-strip.log` and `compiler.log`: the locked canonical Mojo
  test passes 7,574 oriented paths / 243,888 path-edge instances on 120
  specimens. It checks all 7,574 entrances and 42,234 shared suffix edges
  with the actual indexed full-Parikh/Perron verifier. Every repeated
  suffix is compared, including all indices and target letters/offsets,
  to the checked common suffix. Thus 49,808 geometry checks certify all
  243,888 instances by exact composition, rather than assuming suffixes.
* `probe.json`: independent literal-word/Fraction replay checks every
  edge instance of every oriented path, without native suffix factoring.
  Counts and per-member totals match. Its separate finite profile uses
  the immutable 22 completed parent graphs and records their digest.
  These 120 path specimens are not 120 newly completed graphs.
* `symbolic.json`: coefficientwise typed RUN-shear checks for nine source
  types times three bottom occurrence kinds, plus all genuine reversals
  (54 oriented cases); the two concrete entrance schemas including p=0;
  seven exact nonnegative linear implication certificates for ordinal
  guards and negative-sector radius; one root/shift identity modulo the
  exact cubic. The strict geometry inequalities are a written proof,
  not a full Lean formalization. #437's separate finite-rank/Lean work
  is not duplicated.
* `python-tests.log`: all four new research tests pass. They replay the
  packet, exercise attained first/final RUN endpoints and all parameter
  faces, and reject wrong offsets, reversal indices, domains, exhausted
  path caps, nonzero polynomial mutations and negative cone weights.
* `native-initial-compile-failure.log`: the first test source used
  unsupported list destructuring in a negative-control loop. Indexed
  access repaired it; the complete final native regression then passed.
* `governance.log`: the same six existing README consistency findings as
  the parent. They are not new research findings or a green full audit;
  #437 addresses them separately. Proof-bank freshness, vendored pins
  and new Markdown source/relative-link checks pass in `integrity.log`.
* `dependency-status.json`: fresh predecessor and parent heads, with
  #428/#430/#431/#432/#433 still open and no universal identity promotion.
  Hosted exact-head CI remains separate from these local receipts.
* `source-provenance.json`: hashes bind new sources and load-bearing
  parent kernels/oracles, the lockfile and completed graph certificate.

At (0,8), 184 reached oriented sector sources include 142 outside the
previous A_m/unit/signed/E6 local path carrier. The comparison includes
all intermediate vertices on those paths, but does not survey every proof
already on main. Even x/y states with u=1 remain outside these sectors;
their full labels are retained in the profile. No global novelty or
uniform coverage claim follows from the counts.

## Boundary calibration

The exact completed graph at (0,0) contains W=(x,y,2,2,-7)=Z(2,-4,1).
The packet includes a five-edge actual indexed X-to-W witness. W and
formal Q_2 are both strict, but entrance ordinal 0 is FIRST x, not RUN y;
the actual target is (x,x,-1,-5,8). Canonical and independent verifiers
reject the proposed Q_2 target. This is a counterexample to waiving RUN
guards, not an obstruction to W's productivity. The broader inherited
LAST/RUN, invalid-ordinal, overflow and cap controls remain unchanged.

## Deterministic replay

    python -m pip install pytest==8.4.2 sympy==1.14.0
    python -m pytest -q tests/test_class_a_x_cross_strip.py
    python oracles/python/class_a_x_cross_strip.py > /tmp/cross-strip-probe.json
    cmp /tmp/cross-strip-probe.json evidence/class-a-x-cross-strip-2026-10-31/probe.json
    python oracles/python/class_a_x_cross_strip_symbolic.py > /tmp/cross-strip-symbolic.json
    cmp /tmp/cross-strip-symbolic.json evidence/class-a-x-cross-strip-2026-10-31/symbolic.json
    cd kernel
    pixi run --locked mojo run -I . tests/test_class_a_x_cross_strip.mojo

Specimens: k=0..12,t=0..8 plus (0,20),(0,64),(32,0); every allowed
integer p and s and both orientations. Fixed machine integers and the
10,000-edge default path cap refuse a verdict on overflow/exhaustion;
the unbounded theorem is the separate symbolic/written derivation.
