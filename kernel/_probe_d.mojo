from std.sys import argv
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import (build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables, first_left_aligned_depths)
from psc.vertex_coincidence import length_matrix, offset_vector

def main() raises:
    var a=argv(); var d=Int(a[1]); var eps=Int(a[2]); var lo=Int(a[3]); var hi=Int(a[4])
    for n in range(lo,hi+1):
        var tables=build_seed_overlap_tables_screened(class_member(CLASS_A,n+d,n,n+eps))
        var g=build_seed_overlap_graph_from_tables(tables,20000)
        if g.capped:
            print("CAPPED",d,eps,n); continue
        var ds=first_left_aligned_depths(g); var lm=length_matrix(tables)
        var mx=0; var bad=0
        for i in range(g.size()):
            if ds[i]<0: bad+=1
            mx=max(mx,ds[i])
            var v=g.states[i]; var w=offset_vector(lm,v.shift)
            print("V",n,v.top,v.bottom,w[0],w[1],w[2],ds[i])
        print("SUMMARY",d,eps,n,g.size(),mx,bad)
