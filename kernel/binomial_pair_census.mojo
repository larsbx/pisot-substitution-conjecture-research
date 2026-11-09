"""Exact census of irreducible distinct binomially equivalent word pairs.

Experiment A of `docs/c4-solidify-stop-go-2026-11-07.md` (§0, §3.5, §3.6),
reported in `docs/c4-binomial-minimal-pairs-2026-11-07.md`. Kernel:
`psc/binomial_pairs.mojo`.

For each alphabet size `d` and length `n` in the window, the unordered pairs
`{u, v}`, `u != v`, `|u| = |v| = n`, balanced and irreducible, counted by
first scattered-subword defect degree `2`, `3`, `4`, `5+`
(`psc.defect_degree`), with the symmetry classes under
`S_3 x <reversal> x <swap>` of the `K_2 = 0` pairs, the minimal length of
each degree, the four scratch items of the gate (§3.6), the binary
calibration (the closed form `2 C_{n-1}` and Table I of Chrisnata et al.),
and the controls of §3.5.

Replay (from `kernel/`):

    pixi run --locked mojo run -I . binomial_pair_census.mojo            # d = 3, n <= 12; d = 2, n <= 20
    pixi run --locked mojo run -I . binomial_pair_census.mojo 14 20      # extension d = 3, n = 13, 14

`TERNARY_MAX` above 12 is the stated extension (gate §3.6 item (iv)): there
the degree-3 pairs of `n >= 13` are counted, not kept, and their symmetry
classes are not reported. A length outside the window is printed as
`NOT_ENUMERATED`, never as zero. Every calibration disagreement, and every
internal disagreement of the kernel, aborts the run.
"""

from std.sys import argv

from psc.binomial_pairs import (
    LengthCensus,
    binary_closed_form_ordered,
    census_length,
    contains_pair,
    digits,
    g_canonical,
    g_representatives,
    is_irreducible_pair,
    minimal_length,
    orbit_representatives,
    scattered_count,
    table_i_d3,
    table_i_d4,
    thue_morse_block,
)
from psc.bpa import coincidence_boundaries
from psc.defect_degree import DEGREE_FIVE_PLUS, DEGREE_FOUR, DEGREE_THREE, DEGREE_TWO, first_defect_degree
from psc.seeds import length7_seeds
from psc.words import Pair

comptime TERNARY_WINDOW = 12
comptime BINARY_WINDOW = 20
comptime TERNARY_EXTENSION_MAX = 14


def degree_name(degree: Int) -> String:
    return "5plus" if degree == DEGREE_FIVE_PLUS else String(degree)


def csv_ints(values: List[Int]) -> String:
    var out = String("")
    for i in range(len(values)):
        out += ("," if i > 0 else "") + String(values[i])
    return out


def run_alphabet(alphabet: Int, n_max: Int, keep_all_to: Int) raises -> List[LengthCensus]:
    """Rows `n = 1 .. n_max`; pairs of every `K_2 = 0` degree are kept up to
    `keep_all_to`, and only degree `>= 4` beyond it."""
    var rows = List[LengthCensus]()
    for n in range(1, n_max + 1):
        var kept_from = DEGREE_THREE if n <= keep_all_to else DEGREE_FOUR
        rows.append(census_length(alphabet, n, kept_from))
    return rows^


def print_rows(rows: List[LengthCensus]) raises:
    for r in range(len(rows)):
        ref c = rows[r]
        var line = "ROW d=" + String(c.alphabet) + " n=" + String(c.n)
        line += " words=" + String(c.words)
        line += " classes_N2=" + String(c.classes2) + " classes_N3=" + String(c.classes3) + " classes_N4=" + String(c.classes4)
        line += " candidates=" + String(c.candidates)
        line += " irreducible_ordered=" + String(c.irreducible_ordered) + " irreducible_unordered=" + String(c.total)
        line += " degree2=" + String(c.count(DEGREE_TWO)) + " degree3=" + String(c.count(DEGREE_THREE))
        line += " degree4=" + String(c.count(DEGREE_FOUR)) + " degree5plus=" + String(c.count(DEGREE_FIVE_PLUS))
        var degrees: List[Int] = [DEGREE_THREE, DEGREE_FOUR, DEGREE_FIVE_PLUS]
        for t in range(len(degrees)):
            var d = degrees[t]
            if d >= c.kept_from:
                line += " gclasses" + degree_name(d) + "=" + String(len(g_representatives(c.pairs_of_degree(d))))
            else:
                line += " gclasses" + degree_name(d) + "=not_kept"
        print(line)


def print_minimal(rows: List[LengthCensus], alphabet: Int, n_max: Int):
    var degrees: List[Int] = [DEGREE_TWO, DEGREE_THREE, DEGREE_FOUR, DEGREE_FIVE_PLUS]
    for t in range(len(degrees)):
        var m = minimal_length(rows, degrees[t])
        var line = "MINIMAL d=" + String(alphabet) + " degree=" + degree_name(degrees[t])
        if m == 0:
            line += " none_for_n<=" + String(n_max) + " (not a statement beyond the window)"
        else:
            line += " n=" + String(m)
        print(line)


def print_pairs(label: String, pairs: List[Pair]):
    for i in range(len(pairs)):
        print(label + " " + pairs[i].key())


def print_classes(label: String, pairs: List[Pair]):
    """One line per `G`-class: its least element and its size among `pairs`."""
    var reps = g_representatives(pairs)
    for r in range(len(reps)):
        var size = 0
        for i in range(len(pairs)):
            if g_canonical(pairs[i]) == reps[r]:
                size += 1
        print(label + " " + reps[r].key() + " size=" + String(size))


def find_row(rows: List[LengthCensus], n: Int) -> Int:
    for r in range(len(rows)):
        if rows[r].n == n:
            return r
    return -1


def binary_calibration(rows: List[LengthCensus]) raises:
    """Abort unless the binary rows meet the closed form, Table I and the
    theorem `binary_no_equiv2` (no binary irreducible pair has `K_2 = 0`)."""
    var d3 = table_i_d3()
    var d4 = table_i_d4()
    for r in range(len(rows)):
        ref c = rows[r]
        if c.n >= 2 and c.irreducible_ordered != binary_closed_form_ordered(c.n):
            raise Error("CALIBRATION FAILED: binary ordered irreducible count at n = " + String(c.n))
        if c.k2_zero() != 0:
            raise Error("CALIBRATION FAILED: a binary irreducible pair with K2 = 0 at n = " + String(c.n))
        if c.n >= 3 and c.classes3 != d3[c.n - 3]:
            raise Error("CALIBRATION FAILED: binary (N1,N2,N3) classes differ from Table I D_3 at n = " + String(c.n))
        if c.n >= 4 and c.classes4 != d4[c.n - 4]:
            raise Error("CALIBRATION FAILED: binary (N1..N4) classes differ from Table I D_4 at n = " + String(c.n))
    var top = rows[len(rows) - 1].n
    print("CALIBRATION binary irreducible_ordered = 2*C(n-1) for n=2.." + String(top) + ": ok")
    print("CALIBRATION binary K2=0 irreducible pairs = 0 for n=1.." + String(top) + " (binary_no_equiv2): ok")
    print("CALIBRATION binary classes_N3 = Table I D_3(n) for n=3.." + String(top) + ": ok")
    print("CALIBRATION binary classes_N4 = Table I D_4(n) for n=4.." + String(top) + ": ok")


def deck_import_line(rows: List[LengthCensus], alphabet: Int):
    """Least `n` with fewer `(N_1..N_r)` classes than words, `r = 2, 3, 4`,
    against the imported `S(2), S(3), S(4) = 4, 7, 12`."""
    var expected: List[Int] = [4, 7, 12]
    var found = List[Int]()
    for r in range(3):
        var m = 0
        for t in range(len(rows)):
            var classes = rows[t].classes2 if r == 0 else (rows[t].classes3 if r == 1 else rows[t].classes4)
            if classes < rows[t].words:
                m = rows[t].n
                break
        found.append(m)
    var verdict = "consistent" if found == expected else "INCONSISTENT"
    print("IMPORT d=" + String(alphabet) + " least n with a distinct ~r pair, r=2,3,4: " + csv_ints(found) + " (S(r) = 4,7,12 imported): " + verdict)


def print_controls() raises:
    # positive control of the degree classifier (LLR Lemma 30)
    for k in range(1, 5):
        var p = Pair(thue_morse_block(k, 0), thue_morse_block(k, 1))
        var line = "CONTROL thue_morse k=" + String(k) + " degree=" + degree_name(first_defect_degree(p))
        line += " irreducible=" + String(is_irreducible_pair(p))
        if k == 4:
            # K5 != 0 at the coordinate 01010 (scattered count, degree five)
            var x: List[Int] = [0, 1, 0, 1, 0]
            line += " K5_01010=" + String(scattered_count(p.u, x) - scattered_count(p.v, x))
        print(line)
    # negative controls of the irreducibility filter
    var reducible: List[String] = ["0110", "1001", "0110001", "1000110", "012120", "120012"]
    for i in range(0, len(reducible), 2):
        var p = Pair(digits(reducible[i]), digits(reducible[i + 1]))
        print("CONTROL reducible " + p.key() + " degree=" + degree_name(first_defect_degree(p)) + " boundaries=" + csv_ints(coincidence_boundaries(p.u, p.v)) + " irreducible=" + String(is_irreducible_pair(p)))


def main() raises:
    var args = argv()
    var ternary_max = TERNARY_WINDOW
    var binary_max = BINARY_WINDOW
    if len(args) > 1:
        ternary_max = Int(args[1])
    if len(args) > 2:
        binary_max = Int(args[2])
    if ternary_max < 1 or ternary_max > TERNARY_EXTENSION_MAX or binary_max < 4 or binary_max > BINARY_WINDOW:
        raise Error("window: TERNARY_MAX in 1.." + String(TERNARY_EXTENSION_MAX) + ", BINARY_MAX in 4.." + String(BINARY_WINDOW))

    print("BINOMIAL_PAIR_CENSUS unordered {u,v}, u != v, |u|=|v|=n, balanced, irreducible; first defect degree 2,3,4,5plus (5plus: K2=K3=K4=0)")
    print("WINDOW d=3 n<=" + String(ternary_max) + " d=2 n<=" + String(binary_max) + (" (d=3 n>" + String(TERNARY_WINDOW) + " is the extension: degree-3 pairs counted, not kept)" if ternary_max > TERNARY_WINDOW else ""))

    var ternary = run_alphabet(3, ternary_max, TERNARY_WINDOW)
    var binary = run_alphabet(2, binary_max, binary_max)
    print_rows(binary)
    print_rows(ternary)
    print_minimal(binary, 2, binary_max)
    print_minimal(ternary, 3, ternary_max)
    binary_calibration(binary)
    deck_import_line(binary, 2)
    deck_import_line(ternary, 3)

    # the four scratch items of gate §3.6
    var m3 = minimal_length(ternary, DEGREE_THREE)
    var m4 = minimal_length(ternary, DEGREE_FOUR)
    var m5 = minimal_length(ternary, DEGREE_FIVE_PLUS)
    print("ITEM (i) d=3 least n with an irreducible K2=0 pair: " + (String(m3) if m3 > 0 else "none_in_window"))
    var least3 = m4 if m5 == 0 or (m4 > 0 and m4 < m5) else m5
    print("ITEM (i) d=3 least n with an irreducible ~3 pair (degree >= 4): " + (String(least3) if least3 > 0 else "none_in_window"))

    var r7 = find_row(ternary, 7)
    if r7 >= 0:
        var listed = ternary[r7].pairs_of_degree(DEGREE_THREE)
        var seeds = length7_seeds()
        var all_seeds_listed = True
        for i in range(len(seeds)):
            if not contains_pair(listed, seeds[i]):
                all_seeds_listed = False
        var k2zero7 = ternary[r7].k2_zero()
        print("ITEM (ii) d=3 n=7 K2=0 irreducible unordered pairs: " + String(k2zero7) + "; the six psc.seeds pairs all listed: " + String(all_seeds_listed) + "; list equals the seeds: " + String(all_seeds_listed and k2zero7 == len(seeds)) + "; classes under relabelling x swap: " + String(len(orbit_representatives(listed, False))) + "; G-classes (with reversal): " + String(len(g_representatives(listed))))
        print_pairs("LIST d=3 n=7 degree=3", listed)
        print_classes("GCLASS d=3 n=7 degree=3", listed)
        var wt = Pair(digits("0112201"), digits("1200112"))
        print("PINNED wTPair 0112201|1200112 listed at n=7 degree 3: " + String(contains_pair(listed, wt)))
    var r12 = find_row(ternary, 12)
    if r12 >= 0:
        ref c = ternary[r12]
        print("ITEM (iii) d=3 n=12 irreducible ~3 pairs: " + String(c.count(DEGREE_FOUR) + c.count(DEGREE_FIVE_PLUS)) + " (K4 != 0: " + String(c.count(DEGREE_FOUR)) + ", K4 = 0 i.e. ~4: " + String(c.count(DEGREE_FIVE_PLUS)) + ")")
        var four = c.pairs_of_degree(DEGREE_FOUR)
        print_pairs("LIST d=3 n=12 degree=4", four)
        print("ITEM (iii) d=3 n=12 degree-4 classes under relabelling x swap: " + String(len(orbit_representatives(four, False))) + "; G-classes (with reversal): " + String(len(g_representatives(four))))
        print_classes("GCLASS d=3 n=12 degree=4", four)
        var w4 = Pair(digits("011220100112"), digits("120010112201"))
        print("PINNED w4Pair = DEGREE4_STATE 011220100112|120010112201 listed at n=12 degree 4: " + String(contains_pair(four, w4)))
    else:
        print("ITEM (iii) NOT_ENUMERATED (d=3 window below 12)")
    var item4 = String("ITEM (iv) d=3 irreducible ~3 pairs (degree4 + degree5plus) at n=12,13,14:")
    for n in range(12, 15):
        var r = find_row(ternary, n)
        if r < 0:
            item4 += " n=" + String(n) + ":NOT_ENUMERATED"
        else:
            item4 += " n=" + String(n) + ":" + String(ternary[r].count(DEGREE_FOUR) + ternary[r].count(DEGREE_FIVE_PLUS))
            item4 += "(K4=0:" + String(ternary[r].count(DEGREE_FIVE_PLUS)) + ")"
    print(item4)
    for n in range(13, ternary_max + 1):
        var r = find_row(ternary, n)
        print_classes("GCLASS d=3 n=" + String(n) + " degree=4", ternary[r].pairs_of_degree(DEGREE_FOUR))

    print_controls()
    print("NOT_ENUMERATED d=3 n>=" + String(ternary_max + 1) + "; d=2 n>=" + String(binary_max + 1))
