from class_d_plus_positive_b_chambers import _low_wedge
from symbolic_line_certificate import wedge_edges

def main() raises:
    for row in [[0,1,7],[1,7,15],[2,1,7],[3,3,7],[4,3,15]]:
        var edges = wedge_edges(_low_wedge(row[0]),row[1],row[2])
        for i in range(len(edges)):
            print("STRIP",row[0],i,edges[i].coef[0],edges[i].coef[1],edges[i].coef[2],edges[i].coef[3],edges[i].coef[4],edges[i].coef[5])
