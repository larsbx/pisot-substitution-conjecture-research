# Plus-Class-A upper recurrence: source and hypothesis gate

Date: November 15, 2026. Integration base: main
`febe7535afd59cbe56d9ae0bbc541b1bb8b57995`, which merged PR #583.
Problem source: the unchanged
[deferred upper-entry memo](class-a-plus-upper-entry-target-2026-11-14.md)
at `9f0138d213357b866e7ceef0dcbfab96a667526d`.

**Decision: proceed with a central-source recurrence and eventual-cycle
theorem, with literal occurrences and all three coordinates retained.**
Arbitrary strict-source entry into the central slice remains a separate
obligation. This decision precedes new theorem-facing tests and proof code.
It records a research target, not acceptance of the target theorem.

## Sources and existing definitions read first

The current `AGENTS.md`, relevant append-only side notes, the exact
deferred memo, the lower-plus source gate, and the accepted eight-cycle
proof were read before selecting the route. The side-note controls retain
the distinctions between selected recurrence, productive alternative
children, typed coincidence and complete original-prefix paths.

The current `ClassAPlusConstantRecurrence.Nearest A B` is the strict
relation `|c-(-A*a+B*b)|<1/2`. Its negation and uniqueness lemmas impose
no contraction hypotheses. Its `Parameters` structure, however, requires
`0<=A<1/2`, `B>0` and `A+B<1`; those hypotheses cannot be silently reused
throughout the upper region. `yy_run_digit_step` retains actual RUN marks,
original indices and complete integral transport. The new eight-cycle
module supplies exits only at its stated eight parameter-height pairs.

Four primary texts were freshly inspected:

1. **Akiyama and Scheicher, _Symmetric shift radix systems and finite
   expansions_, Mathematica Pannonica 18 (2007), 101–124**, Sections 1, 4
   and 5, especially Theorem 5.2
   ([full primary text](https://www.emis.de/ft/46698)). The symmetric map is
   `tau_r(a,b)=(b,-floor(r1*a+r2*b+1/2))`; its eventual-periodicity set and
   zero-finiteness set are different. Theorem 5.2 gives the exact
   two-dimensional zero-finiteness region. For `0<A<1/4`, `C>0` and
   `r=(A,-C)`, its condition reduces to `C<A+1/2`, or `v>1/2`.
   This is a useful calibration, not a classification of every cycle in
   the complementary chamber. Section 4 gives the standard
   spectral-radius/norm route to eventual periodicity. The author's
   `centralsrs6.pdf` URL timed out; the cited EMIS primary text was read.
2. **Huszti, Scheicher, Surer and Thuswaldner, _Three-dimensional symmetric
   shift radix systems_, Acta Arithmetica 129 (2007), 147–166**, Definition
   1.2, relation (1.2), the two-dimensional region on pages 3–4, and the
   finite graph qualification in Theorem 2.3
   ([author manuscript](https://www.dmg.tuwien.ac.at/nfn/ssrsv10.pdf)).
   It independently records the strict Schur-stability inclusion in the
   symmetric eventual-periodicity set and the asymmetric half-tie
   convention. Its graph construction needs a sufficiently small compact
   parameter region; an arbitrarily large parameter box or capped graph
   does not inherit a completeness theorem.
3. **Kirschenhofer, Petho, Surer and Thuswaldner, _Finite and periodic
   orbits of shift radix systems_, JTNB 22 (2010), 421–448**, introduction,
   companion matrix and inclusion (1.2)
   ([author manuscript](https://www.math.tugraz.at/~tichy/publications/finitev8.pdf)).
   Stable integer recurrences with bounded rounding error and eventual
   periodicity are established methodology. This paper's displayed map
   uses ordinary floor rounding. Its orbit classifications are not
   substituted for the present strict nearest relation or its literal
   substitution realization.
4. **Minervino and Thuswaldner, _The geometry of non-unit Pisot
   substitutions_, AIF 64 (2014), 1373–1417**, Sections 2.2 and 4,
   especially the decomposition set (2.1) and the expansion map following
   Proposition 4.1
   ([publisher text](https://www.numdam.org/article/AIF_2014__64_4_1373_0.pdf)).
   Prefix digits come from actual decompositions `sigma(b)=p a s`, and
   composed expansions follow compatible marked walks. Nonunit geometry
   retains finite-place factors. These facts support literal occurrence
   bookkeeping; they provide no automatic inverse integrality, arbitrary
   central-entry result or spectral conclusion here.

The recurrence method and the zero-finiteness region are prior art. The
proposed contribution is the exact family specialization, its broader
constant-tail classification, and the authenticated occurrence bridge.
No novelty claim for general symmetric shift radix systems is made.

## Exact proposed family and coefficient transfer

Retain `(x,c,y)=(0,1,2)`, bottom-minus-top integral coordinates, and

```text
sigma(x)=x y^(n+d) x,
sigma(c)=c y^n x,
sigma(y)=x y^(n+1) c,
n>=7, n+5<=d<=2n+11,
J=2n+12-d, 1<=J<=n+7.
```

The specialization must prove the actual cubic/root identities, not
receive an arbitrary floating-point field as if it were the family:

```text
chi(X)=X^3-(n+4)X^2+(n-d+5)X-2,
n+4<beta<n+6,
h=1/beta, A=2h, C=beta-(n+4),
v=1+A-C=J/(beta+1)>0,
0<A<2/11<1/4, 0<C<1+A,
Ly=1, Lc=1-h, Lx=3+3h-v.
```

Start with an actual integral `y/y` packet whose physical shift satisfies
`|u|<1/2`. The nearest integer `e` to `beta*u` should be realized by the
original RUN positions `i=1+max(e,0)`, `j=1+max(-e,0)`. Prove `|e|<=n`,
so these positions lie in `1..n+1`. The degree-three identity

```text
beta*u=p*beta^2+(q+r-(n+2)*p)*beta+(p-q)
```

must exclude half-integer ties on the actual inputs. Only then may
nearest rounding commute with negation. The original recurrence is

```text
z[k+2]=nearest(-A*z[k]-C*z[k+1]).
```

With `t[k]=(-1)^k*z[k]`, the transformed relation is exactly the existing
`Nearest A C`:

```text
t[k+2]=nearest(-A*t[k]+C*t[k+1]),
epsilon[k]=t[k+2]-C*t[k+1]+A*t[k], |epsilon[k]|<1/2.
```

It agrees with the symmetric map at `r=(A,-C)` only away from its half
ties. There is no floor-map or tie-convention import without that bridge.

## Proposed elementary boundedness and cycle proof

The earlier memo's impulse-kernel argument remains a valid target for
separate verification, but this increment may use a finite sheared box
instead. This removes the need for a complex-root or infinite-series
formalization without weakening the theorem's hypotheses.

For `J>=5`, `v>2A`, hence `A+C<1`. After proving this exact inequality,
the existing lower-plus coefficient boundedness and constant-tail theorem
apply to the transformed recurrence.

For `J<=4`, prove the stronger family bound `beta>23/2`, giving

```text
A+v < 4/23+8/25 = 284/575 < 1/2.
```

Set `y[k]=2*t[k+1]-t[k]`. The exact updates are

```text
t[k+1]=(t[k]+y[k])/2,
y[k+1]=(C-1/2-2A)*t[k]+(C-1/2)*y[k]+2*epsilon[k].
```

Both second-row coefficients are nonnegative and sum to `1-2v`.
An integral reserve

```text
B=(n+7)*(abs(t[0])+abs(t[1])+1)
```

dominates both initial sheared coordinates and satisfies `2vB>2`.
Prove the invariant box directly, including its initial terms. The
resulting bounded integer pairs and strict-nearest uniqueness give a
repeated pair and an eventually periodic tail.

For a genuinely periodic transformed word, the memo's split at `C=3A`
is available. The small-`C` case reduces to the existing maximum argument
because `A+C<1`. In the large-`C` case, cyclic differences `D[k]` satisfy

```text
S=sum D[k]^2, T=sum D[k]*D[k+1],
sum epsilon[k]*D[k+1]=(1-v/2)*S-A*T,
T<=S.
```

If `S>0`, the right side is at least `S/2`, whereas strict rounding and
integrality make the absolute left side less than `S/2`. The finite cyclic
sum identity and this strict contradiction must be proved, not supplied
as an extremum, graph-finiteness or tail-constancy premise.

Full packet reconstruction uses the actual next-first-coordinate relation:

```text
w[k+1]=(z[k+1], z[k+1]-2*z[k],
        z[k+2]-3*z[k+1]+2*z[k]).
```

A constant transformed tail therefore yields original packets
`W_H=yy(H,3H,-6H)` and `-W_H`, with `H>=0` and `vH<1/2`.
Allow the one-step reconstruction delay: constancy from index `N` gives
the full packet shape from `N+1`. The zero case must be included; the
nonzero case requires the separately authenticated occurrence exits.

## Countercontrols and boundaries

- `A+C<1` is not a whole-upper-region invariant. For example the abstract
  stable recurrence at `A=1/8,C=1` has nonzero constant solutions with
  strict error. Nonzero constants also correspond to the accepted actual
  upper cycle packets. Boundedness or periodicity alone cannot be a zero
  verdict.
- The existing floor tie convention is not odd at half integers. Generic
  rational coefficients can produce a tie; the family needs its own
  degree-three exclusion before sign/parity transfer.
- A reserve based only on the physical shift omits the unbounded integral
  initial data. Retain both `t[0]` and `t[1]`, and the sheared coordinate.
- Reject a minus-family word/field, a sign change in `C`, false coefficient
  inequalities, wrong initial or parity phase, a missing reconstruction
  step, altered complete vectors, and noncomposable prefix histories.
- Preserve the original ordinal control: `sigma(y)[n+2]` is LAST `c`.
  It cannot be relabelled RUN `y`. Reverse both actual indices when using
  reversed escape segments.
- A resource cap, overflow, interval ambiguity or an incomplete cycle
  search must refuse. Finite replay is evidence at its recorded domain;
  it does not prove the unbounded coefficient or initial-pair theorem.

The accepted eight-case suffixes, the proposed wider height decrement,
central recurrence specialization, arbitrary-source central entry, and
`n<=6` upper members retain separate scopes. All original-prefix assembly
must retain the full identity `w_m=M^m*w_0+Q_m-P_m` and the actual ordered
marks. Universal BH #139, A1-prime, C4, G1, PDS and PSC remain outside this
gate. Fresh source-isolated formal acceptance and exact-head hosted
acceptance remain necessary for any newly implemented endpoints.
