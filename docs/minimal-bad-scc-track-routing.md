# Minimal-bad-SCC / inversion-dynamics track routing

**Status:** parallel research-track routing note. This document does **not** add a theorem and does **not** promote the minimal-bad-SCC setup into the main v12.x SCC Producer route.

## Purpose

This note records how to treat the alternative **minimal bad SCC + inversion dynamics** setup relative to the current mass-balance / boundary-synchronization framework.

The setup note studies a more restrictive reductio object: a minimal reachable noncoincident SCC in the small-regime balanced-pair automaton under additional assumptions, including small-regime failure and a minimal-alphabet counterexample. It also introduces inversion profiles, common-cut brackets, and return-map/inversion dynamics. That material targets the same obstruction as SCC Producer, but it uses different hypotheses, different vocabulary, and different machinery.

## Relationship to the current route

The current v12.x route is the **productive direction**:

- allow recurrent noncoincident SCCs to exist;
- prove they produce coincidence siblings;
- use SCC Producer / boundary synchronization to obtain the bridge hypothesis for pure discrete spectrum.

The minimal-bad-SCC track is a **reductio/impossibility direction**:

- assume a minimal bad SCC exists;
- derive rigidity properties from minimality, full support, common-cut recurrence, and inversion dynamics;
- attempt to contradict the existence of the minimal bad SCC.

These are parallel formulations of the same obstruction: a recurrent noncoincident SCC that never produces coincidence. They should not be merged until one route supplies a closed proof.

## Do not import into v12.x

Do **not** import the following into the main v12.x manuscript or proof ladder as load-bearing ingredients:

1. **SRE-failure / minimal-alphabet hypotheses.** They are stronger reductio assumptions and would change the standing scope of the v12.x manuscript.
2. **Inversion profiles and `(M \otimes M)` dynamics.** This is independent machinery, not a replacement for the mass-balance / Parikh-intertwiner framework.
3. **Common-cut bracket vocabulary.** The v12.x route already uses irreducible factorization at coincidence boundaries and two-sided boundary types; adding bracket terminology would create avoidable vocabulary drift.
4. **RS1--RS4 route names.** These belong to the parallel inversion-dynamics program, not to the boundary-synchronization normal form.
5. **Any claim that recurrent noncoincident SCCs are impossible.** The corrected v12.x target is productivity, not SCC elimination.

## Reusable items

Three ideas may be reused later, but only after restating them in the current vocabulary.

### 1. Finite-type recurrence template

The common-cut bracket recurrence argument is a finite-pigeon recurrence template. In the boundary-synchronization route, the corresponding finite types are two-sided boundary-letter types at zero-return boundaries, not common-cut brackets.

Reusable pattern:

> finitely many local types along a recurrent walk imply recurrence of some local type along cycles.

This may help attack the Newborn Synchronizing Boundary conjecture.

### 2. Minimal-alphabet implies full support

Under a minimal-alphabet counterexample assumption, restricted-alphabet inheritance can force full support of every state in the minimal bad SCC. This is not part of v12.x, but it may be useful in a future reductio proof if a boundary-synchronization argument needs full support.

### 3. Return-amplified recognizability

The observation that return padding grows under high iterates while recognizability is controlled may be useful. If used, state it safely as a uniform-radius / large-padding comparison; do not rely on an unaudited equality of recognizability radii for all powers.

## Boundary-synchronization compatibility

Boundary synchronization remains a normal-form/reduction layer, not a completed proof of PSC. The correct ladder is:

```text
Newborn synchronizing boundary  =>  nonsynchronizing-core escape
                                =>  boundary-synchronization lemma
                                =>  SCC Producer
                                =>  bridge hypothesis for PDS
```

The minimal-bad-SCC track may supply future tools for the first arrow, especially finite-type recurrence, but it currently supplies no proof of the arrow.

## Repository policy

When touching v12.x manuscript or proof-state documents:

- keep mass-balance / boundary-synchronization terminology primary;
- cite the minimal-bad-SCC setup, if needed, only as a parallel route;
- never treat inversion dynamics or bracket recurrence as closing SCC Producer unless the missing contradiction is explicitly proved;
- preserve the distinction between proved, conditional, empirical, retired, and parallel-track material.
