from symbolic_line_certificate import ClassLine, certify
from a1_normal_form_census import CLASS_D

def main() raises:
    var first = certify(ClassLine(CLASS_D,[1,1,1,0,1,3]))
    print("BASELINE_CLASS_D_PIN", first.q0,first.symbolic_vertices,first.finite_members,first.finite_non_pip)
    var second = certify(ClassLine(CLASS_D,[3,14,3,15,4,17],True))
    print("BASELINE_NORM_PIN", second.q0,second.symbolic_vertices,second.finite_members,second.finite_non_pip)
