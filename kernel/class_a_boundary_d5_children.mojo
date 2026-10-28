"""D5 complete stars and combined R5/B5 source/image inventories."""
from psc.class_a_boundary_d5_children import certify_d5_children, d5_candidate, d5_image, d5_star_interface, d5_exit_interface
from psc.class_a_boundary_y4_children import y4_image
from psc.class_a_boundary_r5_children import r5_image
from psc.class_a_boundary_b5_children import b5_image


def main() raises:
    certify_d5_children()
    for scope in range(6):
        var labels=d5_candidate(scope==1)
        var name="S43" if scope==1 else "S41"
        if scope==2:
            labels=d5_image()
            name="IMAGE"
        elif scope==3:
            labels=y4_image()
            name="Y4_IMAGE"
        elif scope==4:
            labels=r5_image()
            name="R5_IMAGE"
        elif scope==5:
            labels=b5_image()
            name="B5_IMAGE"
        for w in labels:
            print("CLASS_A_D5_"+name+"_REGISTRY",w.top,w.bottom,w.x,w.c,w.y,d5_star_interface(w),d5_star_interface(w,True),d5_exit_interface(w),d5_exit_interface(w,True))
