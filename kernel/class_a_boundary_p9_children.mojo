"""P9 complete stars, guarded tails and separate star/exit registries."""
from psc.class_a_boundary_p9_children import certify_p9_children, p9_source, p9_companion, p9_image, p9_star_interface, p9_exit_interface
from psc.class_a_boundary_j9_children import j9_image
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,p9_star_interface(w),p9_star_interface(w,True),p9_exit_interface(w),p9_exit_interface(w,True))


def main() raises:
    certify_p9_children()
    var sources=List[BoundaryLabel]()
    for kind in range(2):sources.append(p9_source(kind))
    for kind in range(6):sources.append(p9_companion(kind))
    emit("CLASS_A_P9_SOURCE_REGISTRY",sources)
    emit("CLASS_A_P9_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_P9_IMAGE_REGISTRY",p9_image())
    emit("CLASS_A_P9_J9_IMAGE_REGISTRY",j9_image())
