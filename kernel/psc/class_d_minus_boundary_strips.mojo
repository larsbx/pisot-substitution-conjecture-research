"""The two a=0,1 strips omitted by the a>=2 minus seed carrier."""
from symbolic_line_certificate import ClassLine, LineVerdict, certify
from a1_normal_form_census import CLASS_D


def minus_strip(a: Int) raises -> ClassLine:
    if a != 0 and a != 1:
        raise Error("minus boundary strip selector must be 0 or 1")
    # Parameter n=b-1>=0; the prefix n=0 is the b=1 member, not b=0.
    return ClassLine(CLASS_D,[1,6+3*a,1,7+3*a,1,5+2*a],True)


def certify_minus_strip(a: Int) raises -> LineVerdict:
    var verdict = certify(minus_strip(a))
    if verdict.finite_non_pip != 0 or verdict.finite_outside != 0 or verdict.finite_members != verdict.q0:
        raise Error("minus strip has an uncovered finite-prefix parameter")
    print("MINUS_STRIP_CERTIFIED",a,"n=b-1","threshold",verdict.q0,"vertices",verdict.symbolic_vertices,"finite_pip",verdict.finite_members,"crosschecks",verdict.q0,verdict.q0+5)
    return verdict^


def certify_minus_strips() raises -> List[Int]:
    var result = List[Int]()
    for a in range(2):
        var verdict = certify_minus_strip(a)
        result.append(verdict.q0)
        result.append(verdict.symbolic_vertices)
        result.append(verdict.finite_members)
    print("MINUS_BOUNDARY_STRIPS_CERTIFIED strips=2 a=0,1 b>=1")
    return result^
