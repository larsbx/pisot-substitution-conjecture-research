"""W9 complete stars, constant member image, and uniform image exits."""
from psc.class_a_boundary_w9_children import certify_w9_children, w9_source, w9_companion, w9_image, w9_star_interface, w9_exit_interface
from psc.class_a_boundary_h9_children import h9_image
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,w9_star_interface(w),w9_star_interface(w,True),w9_exit_interface(w),w9_exit_interface(w,True))


def main() raises:
    certify_w9_children()
    var sources=List[BoundaryLabel]()
    for kind in range(2):sources.append(w9_source(kind))
    for kind in range(12):sources.append(w9_companion(kind))
    emit("CLASS_A_W9_SOURCE_REGISTRY",sources)
    emit("CLASS_A_W9_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_W9_IMAGE_REGISTRY",w9_image())
    emit("CLASS_A_W9_H9_IMAGE_REGISTRY",h9_image())
