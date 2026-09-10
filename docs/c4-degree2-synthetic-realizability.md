# C4 degree-2 synthetic realizability obstruction

**Status:** exact falsification artifact for algebra-only proof routes. This is **not** a substitution counterexample and does not prove C4, C1, G1, or PSC.

## 1. Purpose

The degree-2 program now has strong linear constraints:

- `P N = M P` with rank-three Parikh data;
- `Q S = (Lambda^2 M) Q` with rank-three degree-2 defect data;
- `N=A+B`, `S=A-B`, `A,B>=0`;
- `N == S (mod 2)`;
- endpoint nonsynchronization must persist in finite synchronization quotients.

A natural risk is to keep strengthening these matrix conditions and mistake their eventual complexity for the missing theorem. This note gives an explicit three-state object satisfying all of the above, together with actual irreducible balanced-word representatives for each state. It then shows exactly where realization fails: the same substitution incidence matrix cannot realize the required pair of endpoint maps by any ordering of its images.

Thus the remaining obstruction is genuinely **simultaneous word/substitution realization**, not merely matrix realizability or per-state balanced-word realizability.

## 2. Tribonacci incidence and signed child matrices

Use

```text
N = M = [1 1 1]
        [1 0 0]
        [0 1 0]
```

with characteristic polynomial

`x^3-x^2-x-1`.

Choose signed incidence

```text
S = [-1 -1 -1]
    [ 1  0  0]
    [ 0 -1  0].
```

Then

```text
A=(N+S)/2 = [0 0 0]
              [1 0 0]
              [0 0 0],

B=(N-S)/2 = [1 1 1]
              [0 0 0]
              [0 1 0].
```

The ordered signed abstract derived substitution is

```text
T0 -> T0^- T1^+
T1 -> T0^- T2^-
T2 -> T0^-.
```

The cocycle is genuinely nontrivial and not an anti-gauge: the negative self-loop at `T0` already obstructs an ordinary gauge, while the positive edge `T0->T1` together with the negative edge `T1->T0` obstructs the constant `-1` phase gauge.

## 3. Actual irreducible balanced-word representatives

The template uses three normalized balanced states, written with one-based letters:

```text
T0 = (131212, 211123)
T1 = (11213, 21311)
T2 = (112, 211)
```

Each pair has no proper balanced prefix and is therefore irreducible.

Their common Parikh columns are

```text
P = [3 3 2]
    [2 1 1]
    [1 1 0],
```

and their degree-2 defects in basis `(12,13,23)` are

```text
Q = [ 2 2 2]
    [-2 2 0]
    [-2 0 0].
```

Both are invertible over `Q`. Direct exact checks give

`P N = M P`

and

`Q S = (Lambda^2 M) Q`.

So the template is not merely a pair of abstract matrices: every state column is realized by an actual irreducible balanced pair with exactly the required Parikh and `K2` data.

## 4. Abstract endpoint quotient compatibility

The state first-letter pairs are all `{0,1}` in zero-based notation. They are nonsynchronizing for endpoint type F with representative

`h_+=(1,0,0)`.

The last-letter pairs are

```text
T0: {1,2}
T1: {0,2}
T2: {0,1}.
```

They are the three nonsynchronizing pair phases for endpoint type G,

`h_-=(1,2,0)`.

The abstract child selectors are compatible:

- first child: every state goes to `T0`; the unique F quotient-pair phase is fixed as an unordered pair;
- last child: `T0->T1->T2->T0`; G rotates the three unordered nonsynchronizing pair phases in exactly the same cycle.

Thus the template also passes the finite endpoint-signature dynamics used by C4.

## 5. Where realization fails

The incidence matrix `M` fixes the multisets of the three substitution images:

```text
sigma(1): {1,2}
sigma(2): {1,3}
sigma(3): {1}.
```

There are therefore only four possible substitutions with this incidence matrix:

```text
12 / 13 / 1
12 / 31 / 1
21 / 13 / 1
21 / 31 / 1.
```

Their endpoint-type pairs are exactly

```text
A/G, B/F, F/B, G/A.
```

In every ordering at least one endpoint map is globally synchronizing (A or B). The proved global-endpoint theorem therefore rules out a strict nonproductive SCC immediately.

The abstract F/G endpoint regime required by the synthetic signed template is **not realizable by any substitution ordering with the same incidence matrix**.

This is the decisive failure.

## 6. Interpretation

The artifact passes:

1. the Perron/Parikh quotient;
2. the exterior-square signed quotient;
3. orientation parity and exact positive/negative occurrence counts;
4. actual irreducible balanced-word realization of every state column;
5. abstract nonsynchronizing endpoint-signature dynamics.

It fails only when these ingredients must all come from **one and the same substitution word ordering**.

That sharply identifies the next proof target:

> **Incidence-endpoint-word compatibility.** Show that any rank-three degree-2 signed derived substitution satisfying the strict counterexample conditions cannot be simultaneously realized by actual irreducible balanced states and a PIP substitution whose endpoint maps both remain nonsynchronizing.

Equivalently, the next theorem must couple column multisets, image ordering, zero-return factorization, and endpoint quotient phases. Pure characteristic-polynomial or cone arguments cannot see this obstruction.

## 7. Executable scope

`src/psc_research/synthetic_degree2.py` contains the exact matrices, word states, signed child words, abstract F/G endpoint phases, and enumeration of every substitution ordering with the Tribonacci incidence matrix.

`tests/test_synthetic_degree2.py` verifies every claim above.
