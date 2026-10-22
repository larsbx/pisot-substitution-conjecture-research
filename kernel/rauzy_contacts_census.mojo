"""Exact Rauzy contacts: the box verdict and every tile contact, per specimen.

Usage (from kernel/):
    mojo run -I . rauzy_contacts_census.mojo named   > contacts-named.jsonl
    mojo run -I . rauzy_contacts_census.mojo corpus  > contacts-corpus.jsonl

Each `psc-rauzy-contacts/v1` record carries the box automaton's Theorem Omega
verdict and the exact contacts `R(top) + P(w) ∩ R(bottom) ≠ ∅` of
`psc/rauzy_contacts.mojo`. A contact's drawing coordinates are `hi_i >>
(40 - COORD_BITS)`, within `2^-COORD_BITS + |w|₁ 2^-40` of `P(w)`. `named`
also carries `NAMED_POINTS` fractal points, so a figure can draw each subtile
against its contacts. `corpus` walks the standing 4554-specimen corpus in
canonical order on `parallel_fold` (`PSC_CENSUS_WORKERS`, default 4) and emits
the verdict, the contact counts and the lattice neighbours; non-unimodular
specimens are refused, as their quotient is a solenoid.

`box_productive` is the exact verdict. Pure discrete spectrum follows by
`BoxAutomatonPDSCertificate`; covering degree 1 then follows by the cited
equivalence of Ito--Rao / Barge--Kwapisz, which is not a ledger import.
"""

from std.os import getenv
from std.sys import argv

from parallel_fold.map_fold import parallel_map_fold
from psc.corpus import REGIME_UNIMODULAR_COMPLEX, REGIME_UNIMODULAR_REAL, arithmetic_regime, pip_corpus
from psc.rauzy_contacts import TileContacts, tile_contacts
from psc.rauzy_torus import FrequencyFrame, frequency_frame, incidence_of, rauzy_points
from finite_linear_algebra.mat3 import Mat3

comptime SCHEMA = "psc-rauzy-contacts/v1"
comptime NAMED_POINTS = 8192
comptime COORD_BITS = 16
comptime CITED = "PDS by BoxAutomatonPDSCertificate; covering degree 1 by the cited PDS-tiling equivalence (Ito-Rao 2006; Barge-Kwapisz 2006), not a ledger import"


def _ints(xs: List[Int]) -> String:
    var out = String("[")
    for i in range(len(xs)):
        if i > 0:
            out += ","
        out += String(xs[i])
    return out + "]"


def _pairs(xs: List[List[Int]]) -> String:
    var out = String("[")
    for i in range(len(xs)):
        if i > 0:
            out += ","
        out += _ints(xs[i])
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


def _verdict_fields(t: TileContacts) -> String:
    var v = t.verdict.copy()
    var lattice = 0
    for c in t.contacts:
        if c.is_lattice():
            lattice += 1
    return (
        "\"box_productive\":" + ("true" if v.productive else "false")
        + ",\"box_states\":" + String(v.states)
        + ",\"box_recurrent\":" + String(v.recurrent)
        + ",\"box_coincidence_depth\":" + String(v.coincidence_depth)
        + ",\"contacts\":" + String(len(t.contacts))
        + ",\"lattice_contacts\":" + String(lattice)
        + ",\"lattice_neighbours\":" + _pairs(t.lattice_neighbours())
        + ",\"consequence\":\"" + (CITED if v.productive else "none: the box is not productive") + "\""
    )


def _contact_list(t: TileContacts) -> String:
    """`[top, bottom, w0, w1, w2, x, y]` per contact."""
    var shift = 40 - COORD_BITS
    var rows = List[List[Int]]()
    for c in t.contacts:
        rows.append([c.top, c.bottom, c.w0, c.w1, c.w2, c.hi0 >> shift, c.hi1 >> shift])
    return _pairs(rows)


def _head(kind: String, label: String, sigma: List[List[Int]], m: Mat3) -> String:
    return (
        "\"schema\":\"" + SCHEMA + "\",\"kind\":\"" + kind + "\"," + label
        + ",\"sigma\":" + _sigma(sigma) + ",\"regime\":\"" + _regime(m) + "\""
    )


def _refusal(head: String, err: Error) -> String:
    return "{" + head + ",\"status\":\"refused\",\"reason\":\"" + String(err) + "\"}"


def named_line(name: String, sigma: List[List[Int]]) raises -> String:
    var m = incidence_of(sigma)
    var head = _head("named", "\"name\":\"" + name + "\"", sigma, m)
    var frame: FrequencyFrame
    try:
        frame = frequency_frame(m)
    except e:
        return _refusal(head, e)
    var t = tile_contacts(sigma, frame)
    var points = rauzy_points(sigma, frame, NAMED_POINTS)
    var shift = 40 - COORD_BITS
    var xs = List[Int]()
    var ys = List[Int]()
    var letters = List[Int]()
    for p in points:
        xs.append(p.hi0 >> shift)
        ys.append(p.hi1 >> shift)
        letters.append(p.letter)
    return (
        "{" + head + ",\"status\":\"exact\",\"coord_bits\":" + String(COORD_BITS)
        + ",\"freq_floor\":" + _ints([frame.f0, frame.f1, frame.f2])
        + "," + _verdict_fields(t) + ",\"contact_list\":" + _contact_list(t)
        + ",\"points\":" + String(len(points))
        + ",\"x\":" + _ints(xs) + ",\"y\":" + _ints(ys) + ",\"letter\":" + _ints(letters) + "}"
    )


def corpus_line(index: Int, i: Int, j: Int, k: Int, sigma: List[List[Int]], m: Mat3) raises -> String:
    var label = "\"index\":" + String(index) + ",\"i\":" + String(i) + ",\"j\":" + String(j) + ",\"k\":" + String(k)
    var head = _head("corpus", label, sigma, m)
    var frame: FrequencyFrame
    try:
        frame = frequency_frame(m)
    except e:
        return _refusal(head, e)
    var t = tile_contacts(sigma, frame)
    return "{" + head + ",\"status\":\"exact\",\"freq_floor\":" + _ints([frame.f0, frame.f1, frame.f2]) + "," + _verdict_fields(t) + "}"


struct Lines(Copyable, Movable):
    """Records in canonical order; `failed` is the first index that raised."""

    var lines: List[String]
    var failed: Int

    def __init__(out self):
        self.lines = List[String]()
        self.failed = -1


def merge(a: Lines, b: Lines) -> Lines:
    var out = a.copy()
    for l in b.lines:
        out.lines.append(l)
    if b.failed >= 0 and (out.failed < 0 or b.failed < out.failed):
        out.failed = b.failed
    return out^


def main() raises:
    var args = argv()
    var mode = String(args[1]) if len(args) > 1 else String("named")
    if mode == "named":
        print(named_line("tribonacci", [[0, 1], [0, 2], [0]]))
        print(named_line("flipped_tribonacci", [[1, 0], [2, 0], [0]]))
        print(named_line("smith", [[1], [0, 2], [0, 2, 0, 1]]))
        print(named_line("specimen_3742", [[1, 2, 2], [2, 0, 1], [1, 2]]))
        # Negative control: non-unimodular, so its quotient is a solenoid.
        print(named_line("nonunit_control", [[0, 1, 1], [2, 0], [0]]))
    elif mode == "corpus":
        var corpus = pip_corpus()
        var workers = atol(getenv("PSC_CENSUS_WORKERS", "4"))

        def one(s: Int) {corpus} -> Lines:
            var out = Lines()
            try:
                out.lines.append(corpus_line(corpus[s].index, corpus[s].i, corpus[s].j, corpus[s].k, corpus[s].sigma, corpus[s].incidence))
            except:
                out.failed = s
            return out^

        var r = parallel_map_fold(one, merge, Lines(), len(corpus), workers)
        if r.failed >= 0:
            # replay sequentially so the kernel's own error is raised
            var s = corpus[r.failed].copy()
            _ = corpus_line(s.index, s.i, s.j, s.k, s.sigma, s.incidence)
            raise Error("rauzy contacts census: worker failure did not replay")
        for l in r.lines:
            print(l)
    else:
        raise Error("mode must be `named` or `corpus`")
