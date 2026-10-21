"""Case assembly of the entire minus residual a,b>=0, not universal #139."""
from psc.class_d_minus_boundary_strips import certify_minus_strips
from psc.class_d_minus_seed_cover import verify_minus_seed_cover
from psc.class_d_positive_b_spine import verify_minus_positive_b_spine
from psc.class_d_positive_b_geometry import verify_minus_positive_b_conditional_geometry
from psc.class_d_boundary_template import certify_minus_boundary, template_depths


def minus_residual_region(a: Int, b: Int) raises -> Int:
    if a < 0 or b < 0:
        raise Error("minus residual parameters must be nonnegative")
    if b == 0:
        return 0
    if a == 0:
        return 1
    if a == 1:
        return 2
    return 3


def certify_minus_residual() raises -> List[Int]:
    # Native completion receipt is emitted only after every component returns.
    var boundary = certify_minus_boundary()
    var maximum = 0
    for depth in template_depths(boundary):
        if depth < 0:
            raise Error("b=0 component has a non-hitting vertex")
        maximum = max(maximum,depth)
    print("MINUS_B0_COMPONENT_CERTIFIED a>=0",len(boundary.vertices),boundary.edge_count(),maximum)
    var strips = certify_minus_strips()
    var cover = verify_minus_seed_cover()
    var spine = verify_minus_positive_b_spine()
    var geometry = verify_minus_positive_b_conditional_geometry()
    if spine[0] != cover[0] or geometry[0] != cover[0]:
        raise Error("core cover, descent and geometry refer to different carriers")
    print("MINUS_CORE_BH_CERTIFIED a>=2 b>=1 rank",spine[5])
    print("CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open")
    return [len(boundary.vertices),strips[0],strips[3],cover[0],spine[5]]
