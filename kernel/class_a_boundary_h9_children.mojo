"""H9 complete stars, indexed endpoint multiplicity, and uniform image exits."""
from psc.class_a_boundary_h9_children import certify_h9_children, h9_source, h9_companion, h9_image, h9_star_interface, h9_exit_interface
from psc.class_a_boundary_p9_children import p9_image
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,h9_star_interface(w),h9_star_interface(w,True),h9_exit_interface(w),h9_exit_interface(w,True))


def main() raises:
    certify_h9_children()
    var sources=List[BoundaryLabel]()
    for kind in range(2):sources.append(h9_source(kind))
    for kind in range(6):sources.append(h9_companion(kind))
    emit("CLASS_A_H9_SOURCE_REGISTRY",sources)
    emit("CLASS_A_H9_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_H9_IMAGE_REGISTRY",h9_image())
    emit("CLASS_A_H9_P9_IMAGE_REGISTRY",p9_image())
