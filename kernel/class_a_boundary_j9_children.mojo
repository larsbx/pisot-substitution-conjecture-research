"""J9 complete stars, selected exits and separate source/image registry flags."""
from psc.class_a_boundary_j9_children import certify_j9_children, j9_source, j9_image, j9_star_interface, j9_exit_interface
from psc.class_a_boundary_r3_children import enlarged_candidate
from psc.class_a_boundary_e7_children import e7_image
from psc.class_a_boundary_children import BoundaryLabel


def emit(name: String,labels: List[BoundaryLabel]) raises:
    for w in labels:
        print(name,w.top,w.bottom,w.x,w.c,w.y,j9_star_interface(w),j9_star_interface(w,True),j9_exit_interface(w),j9_exit_interface(w,True))


def main() raises:
    certify_j9_children()
    var sources=List[BoundaryLabel]()
    for kind in range(6):sources.append(j9_source(kind))
    emit("CLASS_A_J9_SOURCE_REGISTRY",sources)
    emit("CLASS_A_J9_CANDIDATE_REGISTRY",enlarged_candidate(True))
    emit("CLASS_A_J9_IMAGE_REGISTRY",j9_image())
    emit("CLASS_A_J9_E7_IMAGE_REGISTRY",e7_image())
