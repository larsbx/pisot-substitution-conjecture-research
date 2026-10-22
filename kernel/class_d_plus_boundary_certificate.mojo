"""Complete plus b=0 line candidate: symbolic a>=7 and exact a=0..6.
Run from kernel/: mojo run -I . class_d_plus_boundary_certificate.mojo
A successful run is a canonical receipt; source alone supplies none.
"""
from psc.class_d_boundary_template import certify_plus_boundary, template_depths


def main() raises:
    var g = certify_plus_boundary()
    var maximum = 0
    for d in template_depths(g):
        maximum = max(maximum,d)
    print("plus b=0 symbolic a>=",g.floor,"vertices",len(g.vertices),"directed_edges",g.edge_count(),"max_half_depth",maximum)
    print("finite prefix a=0..6: uncapped, all hitting")
    print("full labelled directed-support cross-checks: a=7,8")
    print("status=PLUS_BOUNDARY_LINE_CERTIFICATE_COMPLETE; domain=s=+1,b=0,a>=0")
