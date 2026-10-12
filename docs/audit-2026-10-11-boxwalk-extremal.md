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

Sampling is not reliable for this quantity: the large-radius cases are sparse tail/extremal objects.  The constructive route found a constrained exhaustive `n=3, L=3` worst case of radius 8, achieved by a front-loaded skew substitution of the form

```text
sigma = ((0,0,1), (2,2), (2,2,0))
```

within the constrained search family.  This is enough to kill the earlier linear candidates and to show random sampling missed the tail.  It is not enough to infer a closed law.

## Claims retracted or not to re-attempt

The thread explicitly falsified or failed the following proof routes.  They should not be reintroduced as lemmas without new evidence.

1. **Spectral contraction to zero.**  Residuals are bounded but do not contract uniformly at the subdominant eigenvalue rate.  The affine prefix corrections are the same order as the residual.

2. **Common-boundary spacing.**  The claim that consecutive common boundaries are spaced by at most `L` is false; gaps can be much larger.

3. **Set self-similarity of boxes.**  Child boxes are not subsets of parent boxes, and completed-parent vectors are not generally parent box states.  Radius, not set inclusion, is the right invariant.

4. **Absolute specimen-independent box radius.**  No absolute constant should be claimed.  The radius grows with image length and, in extremal cases, more quickly than early random samples suggested.

5. **Closed forms `2(L-2)`, `(n-1)(L-1)`, and depth <= 5.**  These were artifacts of restricted sampling/depth.  The current audit should treat all sampled closed forms as unproven and likely false outside their tested range.

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
- It does not promote the uploaded Python scripts to repository evidence.

The PR should therefore be reviewed as a research-status and roadmap update, not as theorem support.
