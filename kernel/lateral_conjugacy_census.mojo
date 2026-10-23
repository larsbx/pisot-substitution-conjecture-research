"""Move 1 of the lateral strategy: conjugacy transfer from Theorem E's classes.

docs/lateral-generalization-strategy-2026-10-23.md. For every PIP member with
|det M| = 2 of Theorem E's classes A-D in the box p, q, r <= BOUND, compute its
conjugacy class (`psc.conjugacy_orbit`) and check the derived facts, failing
closed on any disagreement:

- classes A, C, D: the class is {sigma} (x and c head their own images, and the
  last letters are never all equal);
- class B: exactly min(p, q, r) + 2 members, the chain sigma, z sigma z^{-1},
  ... of right steps; each satisfies the conjugacy equation on words, keeps
  the incidence matrix, and, apart from sigma, is not catch-up-free.

For class-B members inside Theorem C's region (pure discrete spectrum and G1,
docs/p1b-symbolic-cone-2026-10-08.md), the conjugates inherit pure discrete
spectrum by conjugacy invariance. The census counts those conjugates and how
many fall outside both the Theorem Omega domain (images of length <= 4 or
total length <= 8) and Barge's power/rotation class. This is a bounded
count, not a theorem about the full region: the transfer itself is the
one-line invariance, quantified over the whole of Theorem C.

Usage: `mojo run -I . lateral_conjugacy_census.mojo [BOUND]` (default 30).
"""

from std.sys import argv
from finite_linear_algebra.mat3 import Mat3
from a1_normal_form_census import CLASS_A, CLASS_B, CLASS_C, CLASS_D, class_member
from psc.bpa import substitution_incidence
from psc.conjugacy_orbit import (
    common_last_letter,
    conjugacy_class,
    is_left_conjugate_by,
    same_incidence,
    same_substitution,
    step_right,
)
from psc.one_tile import catch_up_free
from psc.pisot import CubicScreen
from substitution_dynamics.barge_class import barge_witness
from substitution_dynamics.substitution import Substitution


comptime MAX_BOUND = 60
comptime CLASS_CAP = 256


def theorem_c_region(p: Int, q: Int, r: Int) -> Bool:
    """Theorem C's hypothesis on (p, q, r), class B; PIP is checked separately."""
    if r == q + 1:
        return p <= 2 * q + 13 or 2 * p <= 5 * q + 10
    if r == q - 1:
        return p <= 2 * q + 7 or 2 * p <= 5 * q - 5
    return False


def in_omega_domain(sigma: List[List[Int]]) -> Bool:
    """Theorem Omega's union of bounded domains: every image of length <= 4,
    or total image length <= 8. Conjugacy keeps both lengths."""
    var total = 0
    var longest = 0
    for a in range(len(sigma)):
        total += len(sigma[a])
        longest = max(longest, len(sigma[a]))
    return longest <= 4 or total <= 8


struct ClassTally(Copyable, Movable, Writable):
    var name: String
    var members: Int
    var nontrivial: Int
    var conjugates: Int
    var largest: Int

    def __init__(out self, name: String):
        self.name = name
        self.members = 0
        self.nontrivial = 0
        self.conjugates = 0
        self.largest = 0

    def write_to[W: Writer](self, mut w: W):
        w.write("class ", self.name, ": PIP det2 members ", self.members,
                ", with nontrivial conjugates ", self.nontrivial,
                ", conjugates beyond sigma ", self.conjugates,
                ", largest class ", self.largest)


struct BTransfer(Copyable, Movable, Writable):
    var certified: Int
    var conjugates: Int
    var catch_up_free_conjugates: Int
    var outside_omega: Int
    var barge_members: Int
    var new_conjugates: Int

    def __init__(out self):
        self.certified = 0
        self.conjugates = 0
        self.catch_up_free_conjugates = 0
        self.outside_omega = 0
        self.barge_members = 0
        self.new_conjugates = 0

    def write_to[W: Writer](self, mut w: W):
        w.write("Theorem C members ", self.certified,
                "; their conjugates beyond sigma ", self.conjugates,
                " (catch-up-free ", self.catch_up_free_conjugates,
                ", outside Omega ", self.outside_omega,
                "); members with a Barge power/rotation witness ", self.barge_members,
                "; conjugates outside Omega and without Barge witness ", self.new_conjugates)


def check_b_chain(sigma: List[List[Int]], members: List[List[List[Int]]], p: Int, q: Int, r: Int) raises:
    """The class-B class is the right-step chain of length min(p, q, r) + 2."""
    var expected = min(p, min(q, r)) + 2
    if len(members) != expected:
        raise Error("class B conjugacy class has ", len(members), " members, expected ", expected)
    var prev = sigma.copy()
    for k in range(1, expected):
        var z = common_last_letter(prev)
        var t = step_right(prev)
        if not same_substitution(t, members[k]):
            raise Error("class B class is not the right-step chain at step ", k)
        if not is_left_conjugate_by(t, prev, List[Int]([z])):
            raise Error("conjugacy equation fails at step ", k)
        if not same_incidence(t, sigma):
            raise Error("a conjugate changed the incidence matrix")
        if catch_up_free(t):
            raise Error("a nontrivial class-B conjugate is catch-up-free")
        prev = t^
    if common_last_letter(prev) >= 0:
        raise Error("the class-B chain did not end")


def census(bound: Int) raises -> Tuple[List[ClassTally], BTransfer]:
    if bound < 1 or bound > MAX_BOUND:
        raise Error("bound must lie in 1..", MAX_BOUND)
    var screen = CubicScreen()
    var names = List[String](["A", "B", "C", "D"])
    var tallies = List[ClassTally]()
    var b = BTransfer()
    for cls in [CLASS_A, CLASS_B, CLASS_C, CLASS_D]:
        var tally = ClassTally(names[cls])
        for p in range(bound + 1):
            for q in range(bound + 1):
                for r in range(bound + 1):
                    var sigma = class_member(cls, p, q, r)
                    var m = Mat3(substitution_incidence(sigma))
                    if abs(m.det()) != 2 or not screen.is_pip(m):
                        continue
                    tally.members += 1
                    var members = conjugacy_class(sigma, CLASS_CAP)
                    var extra = len(members) - 1
                    tally.largest = max(tally.largest, len(members))
                    if cls != CLASS_B:
                        if extra != 0:
                            raise Error("class ", names[cls], " member has a nontrivial conjugate at ", p, ",", q, ",", r)
                        continue
                    check_b_chain(sigma, members, p, q, r)
                    tally.nontrivial += 1
                    tally.conjugates += extra
                    if not theorem_c_region(p, q, r):
                        continue
                    b.certified += 1
                    b.conjugates += extra
                    var barge = barge_witness(Substitution(sigma.copy(), 3), 2).found()
                    if barge:
                        b.barge_members += 1
                    for k in range(1, len(members)):
                        if catch_up_free(members[k]):
                            b.catch_up_free_conjugates += 1
                        if not in_omega_domain(members[k]):
                            b.outside_omega += 1
                            if not barge:
                                b.new_conjugates += 1
        tallies.append(tally^)
    return (tallies^, b^)


def main() raises:
    var args = argv()
    var bound = Int(String(args[1])) if len(args) > 1 else 30
    var result = census(bound)
    print("lateral conjugacy census, p,q,r <=", bound)
    for t in result[0]:
        print(t)
    print(result[1])
