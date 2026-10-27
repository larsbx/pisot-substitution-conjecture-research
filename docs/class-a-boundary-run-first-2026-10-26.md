# Class-A boundary T_m — run/first actual child completion (2026-10-26)

**Status:** all-parameter, one-kind theorem continuation of PR #349 (stacked upon PR #348), not a complete finite carrier, descending rank, target-aware boundary hit, or general PSC. Human review pending. Pinned source branch `research/class-a-boundary-run-first-2026-10-26`. Reuses the targeted literature stop/go in `docs/class-a-boundary-child-carrier-2026-10-26.md`; no new external transfer is claimed.

## Work shown

### Assumptions and hypotheses
Class A `x -> x y^(n+d) x, c -> c y^n x, y -> x y^(n+eps) c`, with `eps=+-1`, `k,t>=0`, `n=k+3+t` minus and `n=2(k+2)+t` plus, `d=2n+6eps+5-k`, `N=n+eps`. The two genuinely realized seed run/run child labels are `T_m=(y,y,-1,1,m)` for `m=r,r+1`, with `r=floor(u)`, `u=d/(beta-1)`. Actual top run ordinal `i` lies in `1..N`. Literal word and exact Perron geometry are independently checked. No unimodularity, global length independence, FI, or real-only non-unit transfer.

### Derivation / reduction

Write `B=beta(m-u)`, `a=Lx/Ly=alpha+2+eps/beta`, `alpha=beta-(n+3+eps)`. The **necessary and sufficient** strict interval-overlap guard for top run y at index `i` and bottom first x is

[
i-1 < B < a+i,qquad 1le ile N,
]
equivalently `B-a<i<B+1`. For `m=r<u`, `B<0`, so **all run/first children of T_r are absent**. For `m=r+1`, the following exact integer ranges are necessary and sufficient, intersected with the indicated true word bounds:

| chamber | T_m | complete actual top run ordinals i | count |
|---|---|---|---|
| minus, any k,t | T_2 | k+3..min(k+5,k+t+2) | min(t,3) |
| plus k<=3 | T_3 | 3k+t+3..2k+t+5 | max(0,3-k) |
| plus k>=4 | T_2 | max(1,k-6)..k-3 | min(4,k-3) |

All other T_m run/first stars are empty. No outer-boundary-contact case is admitted.

**Minus derivation.** With `alpha=beta-(n+2)`, the exact bounds are
[
B-a=k+2+3/eta,qquad B+1=k+5+alpha+2/eta.
]
The Perron bracket `n+2<beta<n+3` gives `0<alpha`. To prove `alpha+2/beta<1`, define `G(X)=X^2-(n+3)X+2`. The *polynomial identity*
[
f(X)=(X+1)G(X)+(k+1)X
]
forces `G(beta)<0` since `f(beta)=0` and `beta>1`. Thus `k+2<B-a<k+3` and `k+5<B+1<k+6`; intersect with `1<=i<=N=k+t+2`.

**Plus k>=4 derivation.** PR #349 certifies `v=alpha-2/beta` strictly in `(0,1)`. For T_2,
[
B-a=k-6-3/eta,qquad B+1=k-3+v.
]
Because `beta>n+4>3`, `k-7<B-a<k-6` and `k-3<B+1<k-2`. Intersect with `1<=i<=N=2k+t+5` to obtain the displayed star.

**Plus k<=3 derivation.** Put `w=alpha-3/beta`. Define
[
G_0(X)=X^2-(n+4)X-3,qquad G_1(X)=X^2-(n+5)X-3.
]
The two exact polynomial identities are
[
f(X)=XG_0(X)-(k+t+7)X-2,
]
[
f(X)=(X+1)G_1(X)+(k+2)X+1.
]
At the positive Perron root, these prove `G_0(beta)>0>G_1(beta)`, hence **`0<w<1`**. Therefore
[
B-a=3k+t+2+w quadLongrightarrowquad ige3k+t+3.
]
The upper guard is automatic for all `i<=N`: `B-N=k-1+2alpha-2/beta`. For `k>=1`, `alpha>3/beta` makes this positive. At `k=0`, `f(n+5)=-(t+11)<0`, so `beta>n+5`, `alpha>1` and again `B-N>0`. Thus `i=3k+t+3..N`; at k=3 the interval is empty. The source has real word length `N=n+eps` and no child outside that range is admitted.

Every accepted edge is `(i,0)` and has complete bottom-minus-top packet
[
(y,x,m-1,m+1,mN-d-i+1).
]
This is computed from the *actual ordered substitution prefixes*, not algebraic child-letter agreement alone.

### Evidence and replay
Canonical Mojo `kernel/psc/class_a_boundary_next_run_first.mojo`: builds the three exact polynomial identities in `Q[t,k][X]`, verifies positive coefficient cones and uses previously verified #349 rational margins. Driver: `kernel/class_a_boundary_next_run_first.mojo`. Native test: `kernel/tests/test_class_a_boundary_next_run_first.mojo`, all actual i for 80 parameter members, both T_m; exact Perron and Parikh replay; malformed-certificate / absent-ordinal refusals. Independent Python: `oracles/python/class_a_boundary_next_run_first.py`, `tests/test_class_a_boundary_next_run_first.py`, 320 members including t=40 stress. Workflow: `.github/workflows/class-a-boundary-next-run-first.yml`.

Replay from `kernel/`:
```sh
pixi run --locked mojo run -I . tests/test_class_a_boundary_next_run_first.mojo
pixi run --locked mojo run -I . class_a_boundary_next_run_first.mojo
```
From root:
```sh
python -m pytest -q tests/test_class_a_boundary_next_run_first.py
```
Native hosted compilation/CI receipts at the **exact PR head** are still required; no local Mojo execution is claimed.

### Negative controls
The `m=r` child families are ruled out by `B<0`; minus t=0 has no run/first because its run ends at `i=k+2`; plus k=3 has none; plus k=4 clips the formally possible negative indices down to `i=1`; `k=7` is the first complete 4-choice plus high chamber. Refuse `i=0`, `i>N`, an invalid source m, altered Parikh target, and a deliberately corrupted polynomial identity. A nonempty recurrence does not prove a target path.

### Non-claims / remaining gaps
This closes **only run/first** for the two T_m states. The other kind guards (run/run, run/last, last/first, last/run, last/last) plus all successor labels and a uniform carrier/descent remain open; no artificial finite quotient, uniform spectral gap, or renewed predecessor contraction is invoked. No complete boundary-hitting, C4 hub-residual word, universal #139, #138/A1', G1 or PSC. Pending independent human review remains validation debt, not a research stop.
