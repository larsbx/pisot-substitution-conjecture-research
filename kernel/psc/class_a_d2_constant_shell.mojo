"""Uniform n>=4 Class-A d=2 518-state one-step shell -> 80-state corridor.

Every supplied constant typed source has offset sum s=+1 or -1.
An actual ordered proper-prefix index can have form a*n+b with a=0
(FIRST/early RUN) or 1 (late RUN/LAST). Its prefix-y coefficient is a,
and the chosen top/bottom index slopes differ by -s, cancelling n*s in
M_n*w + bottom_prefix - top_prefix exactly. The complete child is one of
80 independently certified all-n strict states with rank one smaller.

All source rows have two exact quadratic strict overlap margin certificates
throughout 0<h<1/5, not just at finite sampled n. Thus every listed
source hits offset zero within rank<=5 for EVERY integer n>=4.
No all-n seed reachability or entire d2 candidate hitting is asserted.
"""
from psc.class_a_d2_constant_shell_data import shell_rows
from psc.class_a_d2_fixed_corridor_data import corridor_rows
from psc.class_a_d2_fixed_corridor import certify_corridor_rows


def _tile(letter: Int) raises -> List[Int]:
    if letter==0:
        return [1,2,2]
    if letter==1:
        return [1,0,0]
    if letter==2:
        return [1,1,0]
    raise Error("invalid d2 shell tile type")


def _strict_margin(poly: List[Int]) raises:
    if len(poly)!=3:
        raise Error("d2 shell margin has incorrect degree")
    var a=poly[0]
    var b=poly[1]
    var c=poly[2]
    # 25*(1+t)^2 f(t/(5*(1+t))), t>0 for 0<h<1/5.
    var co=List[Int]([25*a,50*a+5*b,25*a+5*b+c])
    var positive=False
    for value in co:
        if value<0:
            raise Error("d2 shell geometric margin not uniformly positive")
        if value>0:
            positive=True
    if not positive:
        raise Error("d2 shell has boundary-only physical intersection")


def _strict_source(row: List[Int]) raises:
    if len(row)!=11:
        raise Error("malformed d2 shell row width")
    var k=row[2]
    var c=row[3]
    var y=row[4]
    var s=k+c+y
    if abs(s)!=1:
        raise Error("d2 shell needs source coordinate sum +/-1")
    var displacement=List[Int]([s,2*k+y,2*k])
    var lt=_tile(row[0])
    var lb=_tile(row[1])
    var left=List[Int]()
    var right=List[Int]()
    for i in range(3):
        left.append(lb[i]+displacement[i])
        right.append(lt[i]-displacement[i])
    _strict_margin(left)
    _strict_margin(right)


def _prefix(letter: Int, slope: Int, constant: Int) raises -> List[Int]:
    """[child,px,pc,y_slope,y_constant] for i=slope*n+constant.

    This is a real zero-based proper-prefix position for EVERY integer
    n>=4, and the child type is constant across the parameter ray.
    """
    if letter<0 or letter>2:
        raise Error("bad parent letter in d2 shell")
    var last_const=3 if letter==0 else 1 if letter==1 else 2
    if slope==0:
        if constant<0 or constant>4:
            raise Error("early d2 proper-prefix index outside uniform 0..4")
    elif slope==1:
        if constant<-3 or constant>last_const:
            raise Error("late d2 index invalid for all n>=4")
    else:
        raise Error("d2 proper-prefix index slope must be 0 or 1")
    if slope==0 and constant==0:
        return [1 if letter==1 else 0,0,0,0,0]
    var first=1 if letter==1 else 0
    var child=(1 if letter==2 else 0) if (
        slope==1 and constant==last_const) else 2
    return [child, 0 if first==1 else 1,
            1 if first==1 else 0, slope, constant-1]


def _actual_child(row: List[Int]) raises -> List[Int]:
    if len(row)!=11:
        raise Error("malformed d2 shell record")
    var s=row[2]+row[3]+row[4]
    if abs(s)!=1:
        raise Error("source sum must be one for the constant shell")
    var top=_prefix(row[0],row[6],row[7])
    var bottom=_prefix(row[1],row[8],row[9])
    if s+bottom[3]-top[3]!=0:
        raise Error("n-dependent d2 shell child has no uniform identity")
    return [
        top[0],bottom[0],
        row[2]+s+bottom[1]-top[1],
        s-row[2]+bottom[2]-top[2],
        2*row[2]+row[4]+bottom[4]-top[4],
    ]


def certify_shell_rows(rows: List[List[Int]], core: List[List[Int]]) raises -> List[Int]:
    if len(rows)!=518:
        raise Error("d2 symbolic one-step shell count changed")
    if len(core)!=80:
        raise Error("d2 productive target core is incomplete")
    var hist=List[Int]([0,0,0,0,0,0])
    var negative=0
    var positive=0
    for i in range(len(rows)):
        var row=rows[i].copy()
        if len(row)!=11 or row[5]<1 or row[5]>5:
            raise Error("d2 shell rank or record shape invalid")
        for j in range(i):
            var earlier=rows[j].copy()
            var same=True
            for x in range(5):
                if earlier[x]!=row[x]:
                    same=False
            if same:
                raise Error("duplicate d2 shell source label")
        _strict_source(row)
        var j=row[10]
        if j<0 or j>=len(core):
            raise Error("selected d2 shell target missing")
        var target=core[j].copy()
        if row[5]!=target[5]+1:
            raise Error("chosen shell child rank does not decrease")
        var predicted=_actual_child(row)
        for c in range(5):
            if predicted[c]!=target[c]:
                raise Error("actual all-n child differs from named productive core target")
        var s=row[2]+row[3]+row[4]
        if s==-1:
            negative+=1
        else:
            positive+=1
        hist[row[5]]+=1
    if hist!=List[Int]([0,0,230,176,106,6]) or negative<=0 or positive<=0:
        raise Error("d2 shell accepted statistics changed")
    print("CLASS_A_D2_UNIFORM_CONSTANT_SHELL", "sources",518,
          "rank_hist=[0,0,230,176,106,6]","core",80,
          "new_real_edges",518,"strict_margins",1036,
          "hit_depth_bound",5,"all_n_ge_4=true",
          "all_n_seed_reachability=false","all_d2_carrier_hitting=false")
    return [518,80,518,1036,5,negative,positive]


def certify_uniform_constant_shell() raises -> List[Int]:
    var core=corridor_rows()
    _=certify_corridor_rows(core.copy())
    return certify_shell_rows(shell_rows(),core)
