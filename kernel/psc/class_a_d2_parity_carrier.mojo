"""Finite-only discovery of parity-sensitive typed carriers for class-A d=2.

For sigma_n=(xy^(n+2)x, cy^nx, xy^(n+1)c), the exact canonical
swap-seed graph at even n=8,12 and odd n=9,13 determines affine
candidate row endpoints in m=floor(n/2). The candidates are then
checked against other *complete exact finite graphs*; this is NOT
a universal closure, reality, reachability or hitting proof.
No interpolation may be promoted without coefficient-checked all-n
geometry, all-child closure and parameter-dependent descent.
"""
from a1_normal_form_census import class_member, CLASS_A
from psc.overlap_seed_patch import build_seed_overlap_tables_screened, build_seed_overlap_graph_from_tables
from psc.vertex_coincidence import length_matrix, offset_vector
from psc.overlap_seed_patch import first_left_aligned_depths


def specimen(n: Int) raises -> List[List[Int]]:
    if n<4 or n>32:
        raise Error("d2 finite specimen requires 4<=n<=32; no unlimited survey")
    return class_member(CLASS_A,n+2,n,n+1)


def _cmp(a: List[Int], b: List[Int]) raises -> Int:
    if len(a)!=5 or len(b)!=5:
        raise Error("typed d2 state identity requires five coordinates")
    for i in range(5):
        if a[i]<b[i]:
            return -1
        if a[i]>b[i]:
            return 1
    return 0


def _sort_rows(mut data: List[List[Int]]) raises:
    # Explicit stable integer lexicographic insertion sort; not a string key.
    for i in range(1,len(data)):
        var selected=data[i].copy()
        var j=i
        while j>0 and _cmp(data[j-1],selected)>0:
            data[j]=data[j-1].copy()
            j-=1
        data[j]=selected


def exact_profile(n: Int, emit: Bool=False) raises -> List[List[Int]]:
    """A complete finite graph, fail-closed on the 20000-state cap."""
    var tables=build_seed_overlap_tables_screened(specimen(n))
    var graph=build_seed_overlap_graph_from_tables(tables,20000)
    if graph.capped:
        raise Error("D2_STATE_BUDGET_EXHAUSTED: no carrier verdict")
    var lm=length_matrix(tables)
    var records=List[List[Int]]()
    for state in graph.states:
        var w=offset_vector(lm,state.shift)
        if len(w)!=3:
            raise Error("invalid d2 integral offset coordinate")
        records.append(List[Int]([state.top,state.bottom,w[0]+w[1]+w[2],w[2],w[0]]))
    _sort_rows(records)
    var ranges=List[List[Int]]()
    for record in records:
        if len(ranges)==0:
            ranges.append(List[Int]([record[0],record[1],record[2],record[3],record[4],record[4]]))
            continue
        var last=len(ranges)-1
        var old=ranges[last].copy()
        var key_equal=(old[0]==record[0] and old[1]==record[1] and
                       old[2]==record[2] and old[3]==record[3])
        if key_equal and old[5]==record[4]:
            raise Error("duplicate typed d2 exact vertex")
        if key_equal and old[5]+1==record[4]:
            var updated=ranges[last].copy()
            updated[5]=record[4]
            ranges[last]=updated
        else:
            ranges.append(List[Int]([record[0],record[1],record[2],record[3],record[4],record[4]]))
    var depths=first_left_aligned_depths(graph)
    var greatest=0
    for depth in depths:
        if depth<0:
            raise Error("finite d2 graph has an offset-zero-free state")
        greatest=max(greatest,depth)
    if emit:
        print("D2_FINITE_SUMMARY",n,"states",graph.size(),"intervals",len(ranges),"max_first_hit",greatest,
              "all_states_hitting=true","universal=false")
        for row in ranges:
            print("D2_INTERVAL",n,row[0],row[1],row[2],row[3],row[4],row[5])
    return ranges


def inferred_template(n0: Int, n1: Int) raises -> List[List[Int]]:
    """Affine endpoints in m=floor(n/2); paired source graphs only."""
    if not ((n0==8 and n1==12) or (n0==9 and n1==13)):
        raise Error("unapproved d2 parity-template source pair")
    var a=exact_profile(n0)
    var b=exact_profile(n1)
    if len(a)!=len(b):
        raise Error("parity graph interval count changes")
    var delta=(n1-n0)//2
    if delta<=0:
        raise Error("invalid parity-index delta")
    var out=List[List[Int]]()
    for i in range(len(a)):
        var left=a[i]
        var right=b[i]
        for j in range(4):
            if left[j]!=right[j]:
                raise Error("parity typed slice/order changed between source graphs")
        var dlo=right[4]-left[4]
        var dhi=right[5]-left[5]
        if dlo%delta!=0 or dhi%delta!=0:
            raise Error("nonintegral affine interpolation: no template")
        var slo=dlo//delta
        var shi=dhi//delta
        out.append(List[Int]([left[0],left[1],left[2],left[3],
                              slo,left[4]-slo*(n0//2),
                              shi,left[5]-shi*(n0//2)]))
    var expected=93 if n0==8 else 87
    if len(out)!=expected:
        raise Error("unexpected parity carrier interval count")
    return out


def certify_finite_parity(n: Int, candidate: List[List[Int]]) raises -> List[Int]:
    """Equal typed intervals and exact graph only for a specified n."""
    if n<6 or n>32:
        raise Error("d2 candidate comparison is finite only, 6<=n<=32")
    var observed=exact_profile(n)
    if len(candidate)!=len(observed):
        raise Error("d2 predicted and actual interval counts differ")
    var m=n//2
    var total=0
    for i in range(len(observed)):
        var pred=candidate[i]
        var actual=observed[i]
        if len(pred)!=8 or len(actual)!=6:
            raise Error("malformed d2 candidate or observation row")
        for j in range(4):
            if pred[j]!=actual[j]:
                raise Error("d2 typed slice mismatch")
        if pred[4]*m+pred[5]!=actual[4] or pred[6]*m+pred[7]!=actual[5]:
            raise Error("d2 affine endpoints disagree with exact graph")
        total+=actual[5]-actual[4]+1
    var expected=20*n+(105 if n%2==0 else 91)
    if total!=expected:
        raise Error("d2 finite parity-size hypothesis contradicted")
    print("D2_PARITY_CANDIDATE_FINITE",n,"rows",len(candidate),"states",total,
          "all_labels_exact=true","general_n_theorem=false")
    return [len(candidate),total]


def finite_parity_study() raises:
    var even=inferred_template(8,12)
    var odd=inferred_template(9,13)
    # n=6 has the same finite vertex count but two adjacent singleton
    # intervals coalesce: compare its complete graph separately.
    var prefix=exact_profile(6,True)
    if len(prefix)!=91:
        raise Error("d2 even-prefix interval count changed")
    for n in [8,10,14,18,24]:
        _=certify_finite_parity(n,even)
    for n in [7,9,11,15,19,25]:
        _=certify_finite_parity(n,odd)
    print("D2_PARITY_STUDY_COMPLETE","even_rows",len(even),"odd_rows",len(odd),
          "parameter_finite_only=true","no_all_n_hitting_claim=true")
