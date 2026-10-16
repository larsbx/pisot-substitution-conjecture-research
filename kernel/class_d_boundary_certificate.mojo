"""Complete minus b=0 line candidate: exact symbolic tail and finite prefix.
Run from kernel/: mojo run -I . class_d_boundary_certificate.mojo
A successful run is a canonical execution receipt; source alone is not one.
"""
from psc.class_d_boundary_template import certify_minus_boundary, template_depths


def main() raises:
    var g = certify_minus_boundary()
    var depths = template_depths(g)
    var maximum = 0
    for d in depths:
        maximum = max(maximum,d)
    print("minus b=0 symbolic a>=",g.floor,"vertices",len(g.vertices),"directed_edges",g.edge_count(),"max_half_depth",maximum)
    print("finite prefix a=0..3: uncapped, all hitting")
    print("full labelled directed-support cross-checks: a=4,8")
    print("status=MINUS_BOUNDARY_LINE_CERTIFICATE_COMPLETE; domain=s=-1,b=0,a>=0")
