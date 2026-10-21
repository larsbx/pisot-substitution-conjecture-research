"""Rauzy fractals on the 2-torus: named point clouds and a corpus lift survey.

Usage (from kernel/):
    mojo run -I . rauzy_torus_census.mojo named   > named.jsonl
    mojo run -I . rauzy_torus_census.mojo corpus  > corpus.jsonl

`named` emits, for each named substitution, `NAMED_POINTS` exact-enclosure
fractal points (coordinates floored to `2^-COORD_BITS`, so each is within
`2^-COORD_BITS + n 2^-40` of the true `D_n`), their subtile letters, and the
lift profile on a `NAMED_GRID x NAMED_GRID` torus. `corpus` walks the standing
4554-specimen PIP corpus at `CORPUS_POINTS` points on a `CORPUS_GRID` grid and
emits one summary line per specimen; non-unimodular specimens are refused.

Status: diagnostic. A lift profile is a finite sample at one resolution and
certifies no covering degree (see psc/rauzy_torus.mojo).
"""

from std.sys import argv

from finite_linear_algebra.mat3 import Mat3
from psc.corpus import REGIME_UNIMODULAR_COMPLEX, REGIME_UNIMODULAR_REAL, arithmetic_regime, pip_corpus
from psc.rauzy_torus import (
    FrequencyFrame,
    LiftProfile,
    frequency_frame,
    incidence_of,
    lift_profile,
    rauzy_points,
    sup_discrepancy_bound,
)

comptime SCHEMA = "psc-rauzy-torus/v1"
comptime NAMED_POINTS = 8192
comptime NAMED_GRID = 64
comptime CORPUS_POINTS = 4096
comptime CORPUS_GRID = 32
comptime COORD_BITS = 16


def _ints(xs: List[Int]) -> String:
    var out = String("[")
    for i in range(len(xs)):
        if i > 0:
            out += ","
        out += String(xs[i])
    return out + "]"


def _sigma(sigma: List[List[Int]]) -> String:
    var out = String("[")
    for a in range(len(sigma)):
        if a > 0:
            out += ","
        out += "\""
        for x in sigma[a]:
            out += String(x)
        out += "\""
    return out + "]"


def _regime(m: Mat3) -> String:
    var r = arithmetic_regime(m)
    if r == REGIME_UNIMODULAR_COMPLEX:
        return "unimodular-complex"
    if r == REGIME_UNIMODULAR_REAL:
        return "unimodular-real"
    return "nonunimodular"


def _frame_fields(frame: FrequencyFrame) -> String:
    return (
        "\"scale_bits\":40,\"freq_floor\":"
        + _ints([frame.f0, frame.f1, frame.f2])
    )


def _profile_fields(profile: LiftProfile) raises -> String:
    var h = profile.histogram()
    var keys = List[Int]()
    var counts = List[Int]()
    for k in range(len(h.counts)):
        if h.counts[k] > 0:
            keys.append(k)
            counts.append(h.counts[k])
    return (
        "\"grid\":" + String(profile.grid)
        + ",\"undecided\":" + String(profile.undecided)
        + ",\"occupied\":" + String(profile.occupied())
        + ",\"lift_keys\":" + _ints(keys)
        + ",\"lift_counts\":" + _ints(counts)
    )


def _refusal(head: String, err: Error) -> String:
    return "{" + head + ",\"status\":\"refused\",\"reason\":\"" + String(err) + "\"}"


def named_line(name: String, sigma: List[List[Int]]) raises -> String:
    var m = incidence_of(sigma)
    var head = (
        "\"schema\":\"" + SCHEMA + "\",\"kind\":\"named\",\"name\":\"" + name
        + "\",\"sigma\":" + _sigma(sigma) + ",\"regime\":\"" + _regime(m) + "\""
    )
    var frame: FrequencyFrame
    try:
        frame = frequency_frame(m)
    except e:
        return _refusal(head, e)
    var points = rauzy_points(sigma, frame, NAMED_POINTS)
    var profile = lift_profile(points, frame.scale, NAMED_GRID)
    var shift = 40 - COORD_BITS
    var xs = List[Int]()
    var ys = List[Int]()
    var letters = List[Int]()
    for p in points:
        xs.append(p.hi0 >> shift)
        ys.append(p.hi1 >> shift)
        letters.append(p.letter)
    return (
        "{" + head + ",\"status\":\"diagnostic\"," + _frame_fields(frame)
        + ",\"points\":" + String(len(points))
        + ",\"sup_bound\":" + String(sup_discrepancy_bound(points))
        + ",\"coord_bits\":" + String(COORD_BITS)
        + ",\"x\":" + _ints(xs) + ",\"y\":" + _ints(ys) + ",\"letter\":" + _ints(letters)
        + "," + _profile_fields(profile)
        + ",\"lifts\":" + _ints(profile.lifts) + "}"
    )


def corpus_line(index: Int, i: Int, j: Int, k: Int, sigma: List[List[Int]], m: Mat3) raises -> String:
    var head = (
        "\"schema\":\"" + SCHEMA + "\",\"kind\":\"corpus\",\"index\":" + String(index)
        + ",\"i\":" + String(i) + ",\"j\":" + String(j) + ",\"k\":" + String(k)
        + ",\"sigma\":" + _sigma(sigma) + ",\"regime\":\"" + _regime(m) + "\""
    )
    var frame: FrequencyFrame
    try:
        frame = frequency_frame(m)
    except e:
        return _refusal(head, e)
    var points = rauzy_points(sigma, frame, CORPUS_POINTS)
    var profile = lift_profile(points, frame.scale, CORPUS_GRID)
    return (
        "{" + head + ",\"status\":\"diagnostic\"," + _frame_fields(frame)
        + ",\"points\":" + String(len(points))
        + ",\"sup_bound\":" + String(sup_discrepancy_bound(points))
        + "," + _profile_fields(profile) + "}"
    )


def main() raises:
    var args = argv()
    var mode = String(args[1]) if len(args) > 1 else String("named")
    if mode == "named":
        print(named_line("tribonacci", [[0, 1], [0, 2], [0]]))
        print(named_line("flipped_tribonacci", [[1, 0], [2, 0], [0]]))
        print(named_line("smith", [[1], [0, 2], [0, 2, 0, 1]]))
        # Negative control: non-unimodular, so its quotient is a solenoid.
        print(named_line("nonunit_control", [[0, 1, 1], [2, 0], [0]]))
    elif mode == "corpus":
        var corpus = pip_corpus()
        for s in corpus:
            print(corpus_line(s.index, s.i, s.j, s.k, s.sigma, s.incidence))
    else:
        raise Error("mode must be `named` or `corpus`")
