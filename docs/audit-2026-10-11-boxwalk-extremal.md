# Audit: finite box-walk certificate and extremal box-size search

Date: 2026-10-11

Status: research audit / salvage note.  This document records what should be kept from the latest PSC thread and what should not be promoted.  It is intentionally theorem-conservative: the thread produced useful proof coordinates and finite-certificate framing, but it did not close SCC Producer or the real-secondary seed-forcing theorem.

## Executive summary

The useful salvage is a sharpened finite-reachability formulation:

```text
real-secondary seed forcing
  = no closed length >= 2 block-child subsystem
  = finite box-walk recurrence to a matched-letter origin.
```

The correct proof object is not spectral contraction, not a one-step monovariant, and not a sampled closed-form box bound.  It is a finite transition graph on imbalance states, with a per-specimen certificate:

1. the imbalance walk is confined to a finite box;
2. deeper inflations add no new box-walk states/edges after saturation;
3. every reachable nonzero box state reaches the matched-letter origin.

If those hold, the SCC emits a length-1 child and is not closed nonproductive.

The major remaining global gap is an a-priori bound on the size/saturation depth of that finite box.  The thread produced several false candidate bounds and one robust next direction: treat the box-size problem as an extremal construction problem rather than a random-sampling curve fit.

## What was already in the repository

The repo already contains the finite-signing parity diagnostic as a separate layer.  That layer classifies signed SCC child matrices into cancellation, Perron-compatible, and Perron-strict cases.  It should remain separate from the box-walk certificate: it is a useful finite-regime diagnostic, not the same mechanism as imbalance recurrence.

No code from the thread is promoted here.  Repository discipline says Mojo is canonical for theorem-support code and Python is an oracle only; the present PR therefore records a research audit and a future implementation plan rather than adding Python-only proof support.

## Salvageable facts and formulations

### 1. Decomposition identity

For inflated words, the imbalance at a cut has the exact form

```text
d_UV(q) = M * comp(q) + partial(q),
```

where

```text
comp(q) = pi(u[:p_U]) - pi(v[:p_V])
```

is the completed-parent contribution and `partial(q)` is the current partial-image remainder.

The partial term is bounded by image length scale, but this alone does not bound the box.  The completed term is off-diagonal in general because `p_U != p_V`; it is not simply a parent box-walk state.

Keep this identity.  It is the right coordinate system.

### 2. Finite box-walk certificate

The right conditional lemma is:

> If a recurrent noncoincident SCC has a saturated finite imbalance transition graph and every reachable nonzero imbalance state can reach the matched-letter origin, then the SCC is productive.

This is the useful replacement for all failed monotonicity and contraction attempts.  Off-origin cycles are harmless if every such cycle retains an escape path to the origin.

### 3. Branch A / Branch B unification

The real-secondary permutation-first-letter branch and the block-child branch are the same finite-reachability core:

```text
A2: every recurrent NC SCC eventually seeds
  <=> no length >= 2 closed block-child subsystem
  <=> no off-origin trapped component in the box-walk graph.
```

A1, the BPA reach-to-seed statement inside an SCC, is a separate connectivity statement and should be tracked separately.

### 4. Extremal-search reframing

The box-size problem should now be phrased as:

```text
For fixed n and L, determine the maximum stabilized imbalance radius among primitive irreducible Pisot substitutions with max image length L.
```

Sampling cannot certify an extremal or saturation bound. **The previously
reported “constrained exhaustive `n=3, L=3` maximum radius 8” is withdrawn
as a mathematical result.** The original constrained enumeration's membership
predicate, search order, saturation/closure criterion, depth and memory
budgets, source program, and output are not preserved. In particular, a
finite-depth plateau does not establish transition closure or stabilization.
Do not cite 8 as an extremum, use it as a proved upper bound, or infer failure
of general radius formulas from that unreplayable report.

We retain the historical example as a **named, reproducible negative
control**, not as a saturated box certificate:

```text
sigma = ((0,0,1), (2,2), (2,2,0))
seed = ((0,1), (1,0))
A_d = sigma^d(0,1), B_d = sigma^d(1,0)
r_d = max_{0 <= q <= |A_d|} ||pi(A_d[:q]) - pi(B_d[:q])||_infty
```

Here the search family is **exactly this one substitution and this one
balanced length-two swap seed**. Every cut `q` is an aligned common-index
prefix cut, measured using exact integer Parikh counts. The deterministic
bounded replay checks **every such cut** for each depth 0 through 9;
`max_depth=9` and `max_symbols_per_side=30000` are hard budgets. It
generates no random samples. The per-depth sequence of
`(word length, aligned radius)` is

```text
d:        0     1     2     3      4      5      6       7       8        9
length:   2     5    14    40    114    324    920    2612    7416    21056
radius:   1     2     4     6      6      6      8       8       8       10
```

The first radius-10 cut at depth 9 is `q=9054`, with exact difference
`(5,5,-10)`. Thus the **aligned-prefix** statistic remains at 8 for
depths 6–8 and *increases to 10 at depth 9*. In particular, radius 8
cannot be an upper bound for this clearly specified aligned-cut statistic
on the named substitution. This does not reconstruct or disprove a
*differently defined* restricted “comp-set” statistic from the missing
historical search: there is no recovered definition to test.

### Progress-dependent bounds remain a live possibility

**The value 8 may describe the progress of an exploration, rather than
the final extremum.** It was the exact aligned-prefix maximum through
inflation depth 8 in the named replay; at depth 9 the maximum becomes 10.
This distinction should not be lost when withdrawing the unsupported
*exhaustive* maximum. The historical constrained-family value 8 might
likewise have been the largest **observed so far** at a particular
enumeration cursor, depth cutoff, or state/length budget, but the
original search metadata are missing and that interpretation remains
**hypothetical**, not reconstructed evidence.

There are two distinct, potentially useful notions of *progress*:

1. **Mathematical depth.** For a fixed substitution and seed, write
   `r_d(sigma,seed)` for the aligned-cut radius at exact inflation depth
   `d`, and `R_<=D = max_{0<=d<=D} r_d` for the cumulative
   progress-indexed radius. `R_<=D` is necessarily nondecreasing in
   `D`, even though monotonicity of the individual `r_d` is not
   established. It gives a **certified lower bound** on
   `sup_d r_d` after all cuts up to `D` have been checked, never an
   infinite-depth upper bound without an independent saturation/closure
   proof. Here `R_<=8 = 8` but `R_<=9 = 10`.
2. **Enumeration progress.** For an explicitly defined family `F`
   and fully evaluated prefix `F_t`, the running record
   `B_t = max_{sigma in F_t} R_<=D(sigma,seed)` is only a lower
   bound on the full-family maximum. It becomes an exact
   **finite-depth finite-family** maximum only when `F_t=F`, every
   member and cut has been examined, the depth budget is stated,
   and every budget refusal is resolved. Neither family exhaustion
   nor finite-depth exhaustion establishes eventual box-walk
   saturation. An unprocessed specimen is not evidence that the
   current record is final.

Thus a **progress-sensitive growth law or computable bound**
`R_<=D <= f(n,L,D)`, or a rigorously justified stopping criterion
derived from graph-state progress, is a legitimate *open research
direction*. It is not ruled out by the failure of a constant bound;
for this particular aligned-cut witness any proposed such
`f(3,3,9)` must be at least 10. No formula, monotonicity of
`r_d`, or finite saturation criterion is asserted here.

Future run receipts must record `F`'s exact membership predicate,
source/commit identifier, ordering or seeded stride, completed
specimens, last enumeration cursor, depth reached, per-state and
word-size budgets, explicit `BUDGET_EXHAUSTED` counts, and distinct
`DEPTH_COMPLETE`, `FAMILY_EXHAUSTED`, and `SATURATED` verdicts.
Only the evidence supporting the stated verdict may be promoted.

**Replay from the repository root** (canonical Mojo; Python is an independent
oracle, not theorem-support authority):

```sh
cd kernel && mojo run -I . boxwalk_radius_probe.mojo
# Or, from the repository root:
python3 oracles/python/boxwalk_radius_probe.py --max-depth 9 --max-symbols 30000
python3 -m pytest -q tests/test_boxwalk_radius_probe_oracle.py
```

Code/output locators:
`kernel/psc/boxwalk_radius_probe.mojo`,
`kernel/boxwalk_radius_probe.mojo`,
`kernel/tests/test_boxwalk_radius_probe.mojo`,
`oracles/python/boxwalk_radius_probe.py`, and
`evidence/boxwalk-radius8-depth9.json` (all exact integer computations).
The Oracle/JSON fixture includes first-maximizing cuts and imbalance vectors
at each depth. Exceeding the resource budget is a **refusal**, not a
mathematical verdict; reaching the chosen depth cap without a witness is
also not a saturation certificate. No closure, all-substitution enumeration,
or global `R*(3,3)`/`R*(3,4)` bound is established.

## Claims retracted or not to re-attempt

The thread explicitly falsified or failed the following proof routes.  They should not be reintroduced as lemmas without new evidence.

1. **Spectral contraction to zero.**  Residuals are bounded but do not contract uniformly at the subdominant eigenvalue rate.  The affine prefix corrections are the same order as the residual.

2. **Common-boundary spacing.**  The claim that consecutive common boundaries are spaced by at most `L` is false; gaps can be much larger.

3. **Set self-similarity of boxes.**  Child boxes are not subsets of parent boxes, and completed-parent vectors are not generally parent box states.  Radius, not set inclusion, is the right invariant.

4. **Absolute specimen-independent box radius.**  No absolute constant should be claimed.  The radius grows with image length and, in extremal cases, more quickly than early random samples suggested.

5. **Closed forms `2(L-2)`, `(n-1)(L-1)`, and depth <= 5.**  The historical sweep did not give replayable disproofs. Treat these formulas as unproved, not independently refuted by the withdrawn “maximum 8.” For any proposed **aligned-prefix** upper bound below 10 at `(n,L)=(3,3)`, the depth-nine witness above is an exact finite counterexample. Other radius definitions require their own replay and quantifiers.

6. **One-step local monovariants.**  Minimum child length, first-letter diagonalization, and one-step length-1 injection all fail as general mechanisms.  The exit is multi-step and recurrence-based.

## Recommended next implementation work

Do not add theorem-support Python-only code.  Implement these as Mojo diagnostics only after the research decision is accepted.

### A. Matrix-first extremal search

Create an exact extremal search for `R*(3,4)`:

1. enumerate incidence matrices first;
2. filter primitive / irreducible / Pisot at the matrix level;
3. enumerate word orderings only for surviving matrices;
4. prioritize layered/front-loaded orderings;
5. compute exact staircase/imbalance closure until saturation;
6. produce a certificate for the extremizer.

Suggested future files:

```text
kernel/boxwalk_extremal_census.mojo
kernel/tests/test_boxwalk_extremal.mojo
```

### B. Certificate output for extremizers

For any claimed extremizer, output:

- substitution images;
- incidence matrix;
- Pisot data;
- radius sequence by depth;
- comp-set size by depth;
- actual box-radius sequence by depth;
- witness pair and cut attaining the radius;
- prefix Parikh vectors at the witness.

### C. Keep the proof target local

The immediate target should be:

```text
certify R*(3,4) and characterize the extremizer structure.
```

Do not fit a law until at least `L=4` is structurally understood.

## Relationship to current PSC proof program

This note does not change the main v12/v12.1/v12.2 framing:

- SCC Producer remains open.
- Boundary synchronization remains a proven local implication but not a global proof.
- The finite signing parity layer remains diagnostic.
- The finite box-walk certificate is a separate recurrence mechanism for the real-secondary/block-child branch.

The useful contribution is narrower:

> It turns the real-secondary/block-child obstruction into a finite certificate problem and identifies extremal box-size enumeration as the next rigorous task.

## What this does not establish

- It does not prove PSC.
- It does not prove SCC Producer.
- It does not prove a uniform box-radius theorem.
- It does not validate any closed-form `R_infty(n,L)` bound.
- It withdraws the historical constrained-family radius-eight maximum; it supplies only an exact, explicitly budgeted single-specimen aligned-prefix negative control.
- It does not promote the uploaded Python scripts to repository evidence.

The PR should therefore be reviewed as a research-status and roadmap update, not as theorem support.
