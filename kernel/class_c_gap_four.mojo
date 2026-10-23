"""Scoped #139 certificates on C (n+4,n,n-3) and (n+4,n,n-5).

Reuse the complete symbolic-line kernel, including the exact finite prefix
and two vertex-set cross-checks. No claim about gaps d>=5 or universal #139.
See docs/issue139-ac-gap4-2026-10-22.md.
"""
from std.sys import argv
from a1_normal_form_census import CLASS_C
from symbolic_line_certificate import ClassLine, LineVerdict, certify


def gap_four(eps: Int) raises -> ClassLine:
    if eps != 1 and eps != -1:
        raise Error("class-C gap-four sign must be +1 or -1")
    return ClassLine(CLASS_C, [1, 4, 1, 0, 1, -4 + eps])


def check_verdict(eps: Int, v: LineVerdict) raises:
    _ = gap_four(eps)
    var expected = List[Int]([49, 201, 6278, 46, 0, 3])
    if eps == -1:
        expected = [85, 216, 7338, 76, 4, 5]
    var actual = List[Int]([v.q0, v.symbolic_vertices, v.queries,
                           v.finite_members, v.finite_non_pip, v.finite_outside])
    if actual != expected:
        raise Error("class-C gap-four verdict differs from its exact pin")


def certify_gap_four(eps: Int) raises -> LineVerdict:
    var v = certify(gap_four(eps))
    check_verdict(eps, v)
    print("CLASS_C_GAP_FOUR", "eps=", eps, "q0=", v.q0,
          "vertices=", v.symbolic_vertices, "sign_reads=", v.queries,
          "prefix_pip=", v.finite_members, "prefix_non_pip=", v.finite_non_pip,
          "prefix_outside=", v.finite_outside,
          "all_admissible_members_hit=true universal_139=false")
    return v^


def main() raises:
    var args = argv()
    if len(args) != 2:
        raise Error("usage: class_c_gap_four.mojo EPS")
    _ = certify_gap_four(Int(args[1]))
