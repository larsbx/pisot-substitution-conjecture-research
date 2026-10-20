from class_d_plus_positive_b_chambers import _high_wedge
from symbolic_line_certificate import wedge_edges

def main() raises:
    var edges = wedge_edges(_high_wedge(),7,0)
    for i in range(len(edges)):
        print("HIGH_STRIP",i,edges[i].coef[0],edges[i].coef[1],edges[i].coef[2],edges[i].coef[3],edges[i].coef[4],edges[i].coef[5])
