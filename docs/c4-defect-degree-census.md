# C4 finite-corpus first-defect census

**Status:** exact finite calibration over the established 4,554-member alphabet-3 PIP corpus with image lengths `<= 3`. This is **not** a proof of a general defect-degree bound, G1, C1, C4, or PSC.

This note records the exact first scattered-subword defect distribution of every reachable noncoincident BPA state in the finite corpus and the normal form of the rare degree-3 states.

## 1. Exact defect-degree distribution

Every balanced-pair state has `K1=0`. `mojo/defect_degree_census.mojo` computes `K2`, `K3`, and `K4` by streaming integer recurrences and classifies the first nonzero defect as degree 2, 3, 4, or `>=5` (meaning zero through degree four).

The exact result is:

| scope | noncoincident states | degree 2 | degree 3 | degree 4 | degree >=5 |
|---|---:|---:|---:|---:|---:|
| all reachable | 385,926 | 385,902 | 24 | 0 | 0 |
| recurrent SCC states | 369,486 | 369,462 | 24 | 0 | 0 |
| noncoincident sink-SCC states | 368,610 | 368,586 | 24 | 0 | 0 |

Across all 4,554 PIP substitutions:

- `0` substitutions have a reachable degree-4-or-higher state;
- `0` have a recurrent degree-4-or-higher state;
- `0` have a sink degree-4-or-higher state;
- all BPA constructions terminate below the established cap.

This is much stronger finite evidence than the abstract balanced-pair universe: an exact irreducible ternary balanced pair of length 12 is known with `K1=K2=K3=0` and `K4!=0`, so first degree four genuinely exists outside this PIP reachability corpus. `tests/test_multidegree_sieve.py` preserves that counter-calibration.

## 2. The 24 degree-3 occurrences

`mojo/degree3_catalog.mojo` prints every reachable state with `K2=0` and `K3!=0`. The exact catalogue has:

- `12` PIP substitutions containing a degree-3 state;
- `24` state occurrences total;
- all `24` recurrent;
- all `24` in the unique noncoincident sink SCC;
- lengths exactly `9` and `19`, two degree-3 states per such substitution.

Thus the live degree-3 phenomenon in this finite corpus is **not** the length-7 seed family from the old Spectral Black Box.

## 3. Relabeling/reversal normal form

`scripts/analyze_degree3_catalog.py` quotients the exact catalogue by alphabet relabeling and checks reversal symmetry.

There are exactly **four normalized state relabeling classes** (Mojo uses zero-based letters):

```text
length 9:
  011202001|120001120
  011212001|120011120

length 19:
  0011202220010011202|2001001120212022001
  0102211211000102211|2110010201022112110
```

There are exactly **two substitution conjugacy classes**:

```text
011 / 2 / 120
1 / 210 / 002
```

The two substitution classes are exchanged by reversing every substitution image. The two length-9 state classes are exchanged by word reversal, and likewise the two length-19 classes.

The six certified length-7 seed pairs form one six-element alphabet-relabeling orbit. **None** of the 24 live degree-3 occurrences lies in that seed orbit.

## 4. Consequence for the proof program

The general signed first-defect theorem remains necessary because degree four exists abstractly. However, within the exact 4,554-PIP reachability corpus, every noncoincident state is already controlled by the degree-2 or degree-3 representation layers:

1. degree 2: `Q2 S = (Lambda^2 M) Q2`;
2. degree 3: `Q3 S = Phi3 Q3` in `W3`.

For a hypothetical **strict closed nonproductive** degree-3 SCC, the orientation bound `rho(S)<=beta` and the rational factorization of `Phi3|W3` force the whole `K3` image into the two-dimensional determinant/centralizer eigenspace. The 24 productive finite-corpus occurrences should therefore be audited against that centralizer condition and their coincidence leakage; that is the next exact diagnostic.

This finite classification does not prove that a general PIP BPA has no degree-4 state, nor that every degree-3 state belongs to the four classes above. It only says those statements hold exhaustively in the stated 4,554-substitution corpus.
