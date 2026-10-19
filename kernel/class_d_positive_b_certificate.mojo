"""Candidate complete certificate for the two positive-b class-D residual wedges.

A successful run proves boundary hitting for every integer point of the selected
wedge: certify_wedge handles one eventual quadrant; wedge_edges returns the
finite family of parameter lines covering its complement; certify(line) proves
each line including its exact finite prefix. Any undecided sign, cap, non-PIP
mismatch or failed hitting verdict raises.
"""
from std.sys import argv
from symbolic_line_certificate import (
    ClassWedge, certify_wedge, wedge_edges, certify,
)
from a1_normal_form_census import CLASS_D


def _certify_complete(name: String, spec: ClassWedge) raises:
    print("BEGIN", name)
    var core = certify_wedge(spec)
    print(
        "core:",
        "a0=", core.a0,
        "b0=", core.b0,
        "vertices=", core.symbolic_vertices,
        "queries=", core.queries,
    )
    var edges = wedge_edges(spec, core.a0, core.b0)
    print("boundary lines:", len(edges))
    var total_finite_pip = 0
    var max_line_q0 = 0
    for i in range(len(edges)):
        var v = certify(edges[i])
        total_finite_pip += v.finite_members
        max_line_q0 = max(max_line_q0, v.q0)
        print(
            "edge", i,
            "q0=", v.q0,
            "vertices=", v.symbolic_vertices,
            "finite_pip=", v.finite_members,
            "non_pip=", v.finite_non_pip,
            "outside=", v.finite_outside,
        )
    print(
        "COMPLETE_POSITIVE_B_WEDGE",
        name,
        "core_a0=", core.a0,
        "core_b0=", core.b0,
        "boundary_lines=", len(edges),
        "finite_prefix_pip=", total_finite_pip,
        "max_line_q0=", max_line_q0,
    )


def main() raises:
    var args = argv()
    var branch = String("both")
    if len(args) == 2:
        branch = String(args[1])
    if len(args) > 2 or (branch != "both" and branch != "plus" and branch != "minus"):
        raise Error("usage: class_d_positive_b_certificate.mojo [both|plus|minus]")
    # c = b - 1 >= 0 in the residual coordinates of the roadmap.
    if branch != "minus":
        _certify_complete(
            "s=+1",
            ClassWedge(CLASS_D, [4,3,1, 3,3,1, 1,2,1]),
        )
    if branch != "plus":
        _certify_complete(
            "s=-1",
            ClassWedge(CLASS_D, [6,3,1, 7,3,1, 5,2,1]),
        )
