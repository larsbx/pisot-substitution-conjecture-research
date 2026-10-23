"""Scoped gap-five C lines; the existing checker alone decides completeness.

See docs/issue139-gap5-2026-10-23.md. A refusal is not non-hitting evidence.
"""
from std.sys import argv
from a1_normal_form_census import CLASS_C
from symbolic_line_certificate import ClassLine, LineVerdict, certify


def gap_five(eps: Int) raises -> ClassLine:
    if eps != 1 and eps != -1:
        raise Error("class-C gap-five sign must be +1 or -1")
    return ClassLine(CLASS_C, [1, 5, 1, 0, 1, -5 + eps])


def certify_gap_five(eps: Int, progress: Bool = False) raises -> LineVerdict:
    var v = certify(gap_five(eps), progress)
    print("CLASS_C_GAP_FIVE", "eps=", eps, "q0=", v.q0,
          "vertices=", v.symbolic_vertices, "sign_reads=", v.queries,
          "prefix_pip=", v.finite_members, "prefix_non_pip=", v.finite_non_pip,
          "prefix_outside=", v.finite_outside,
          "all_admissible_members_hit=true universal_139=false")
    return v^


def main() raises:
    var args = argv()
    if len(args) != 2:
        raise Error("usage: class_c_gap_five.mojo EPS")
    _ = certify_gap_five(Int(args[1]), True)
