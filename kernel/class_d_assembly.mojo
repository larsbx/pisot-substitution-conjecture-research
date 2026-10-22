"""Consume provenance-checked complete receipts and replay the plus b=0 line."""
from std.sys import argv
from psc.class_d_assembly import verify_class_d_receipts
from psc.class_d_boundary_template import certify_plus_boundary


def main() raises:
    var args = argv()
    if len(args) != 3:
        raise Error("usage: class_d_assembly.mojo PLUS_LOG MINUS_LOG; run the provenance checker first")
    var plus: String
    var minus: String
    with open(String(args[1]),"r") as f:
        plus = f.read()
    with open(String(args[2]),"r") as f:
        minus = f.read()
    verify_class_d_receipts(plus,minus)
    var boundary = certify_plus_boundary()
    if len(boundary.vertices) != 718 or boundary.edge_count() != 4326:
        raise Error("plus boundary receipt changed")
    print("CLASS_D_ASSEMBLY_CANDIDATE plus_positive_b=complete minus_residual=complete plus_b0=complete inherited_wedges=ClassDWedgeBoundaryHitting target=offset_zero integration=pending universal_139=open")
