"""Uniform countermodel to a rectangular class-A formal overlap cover.

Written proof: docs/class-a-cover-obstruction-2026-10-21.md. This does not
assert seed reachability or failure of hitting for the formal witnesses.
"""
from psc.class_a_run_index import member, labelled, checked_step, check_symbolic_edge, _same
from psc.param_poly import QX, qx_const, qx_affine, qx_affine2, qx_add, qx_sub, qx_mul, qx_neg
from psc.overlap_seed_patch import build_seed_overlap_tables_screened


def verify_cover_identities() raises:
    var one=qx_const(1)
    var n=qx_affine(0,1)
    var h=qx_affine2(0,0,1)
    var h2=qx_mul(h,h)
    var h3=qx_mul(h2,h)
    var hp=qx_add(one,h)
    var np=qx_add(n,one)
    var p=qx_sub(qx_add(h3,qx_mul(np,qx_add(h,h2))),one)
    # h^3 chi_n(1+1/h) = -P(n,h).
    var cleared=qx_sub(qx_add(qx_sub(qx_mul(qx_mul(hp,hp),hp),qx_mul(qx_mul(qx_add(n,qx_const(4)),qx_mul(hp,hp)),h)),qx_mul(qx_mul(qx_add(n,qx_const(4)),hp),h2)),qx_mul(qx_const(2),h3))
    _same(cleared,qx_neg(p))
    var lx=qx_add(hp,h2)
    var lc=one.copy()
    var ly=hp.copy()
    var mt=List[QX]([
        qx_add(qx_mul(qx_const(2),lx),qx_mul(np,ly)),
        qx_add(qx_add(lx,lc),qx_mul(n,ly)),
        qx_add(qx_add(lx,lc),qx_mul(np,ly)),
    ])
    var lengths=List[QX]([lx.copy(),lc.copy(),ly.copy()])
    for j in range(3):
        _same(qx_sub(qx_mul(h,mt[j]),qx_mul(hp,lengths[j])),p)
    # Actual FIRST/RUN occurrence, with bottom prefix c y^2.
    check_symbolic_edge(0,1,[qx_neg(np),qx_add(n,qx_const(4)),qx_const(-2)],qx_const(0),qx_const(3),0,1,0,2,[qx_neg(n),qx_add(n,qx_const(3)),qx_const(-1)])
    var tv=qx_sub(qx_sub(one,qx_mul(np,qx_mul(h,hp))),qx_mul(qx_const(2),h))
    var tw=qx_sub(qx_sub(qx_const(2),qx_mul(n,qx_mul(h,hp))),h)
    var reduced_v=qx_sub(h3,qx_mul(qx_const(2),h))
    var reduced_w=qx_add(one,qx_add(h2,h3))
    _same(qx_sub(tv,reduced_v),qx_neg(p))
    _same(qx_sub(tw,reduced_w),qx_neg(p))
    _same(qx_add(reduced_v,lc),qx_add(qx_sub(one,qx_mul(qx_const(2),h)),h3))
    _same(qx_sub(lx,reduced_v),qx_sub(qx_add(one,qx_add(qx_mul(qx_const(3),h),h2)),h3))
    _same(qx_add(reduced_w,ly),qx_add(qx_const(2),qx_add(h,qx_add(h2,h3))))
    _same(qx_sub(lx,reduced_w),qx_mul(qx_mul(h,qx_sub(one,h)),hp))
    print("CLASS_A_COVER_IDENTITIES transformed_cubic=true eigenlengths=true occurrence=true strict_margins=true scope=formal_rectangle_countermodel")


def in_rectangle(n: Int, k: Int, c: Int, y: Int) -> Bool:
    return abs(k)<=n+1 and abs(y)<=2 and abs(k+c+y)<=1


def replay_cover_escape(n: Int) raises:
    if n<4:
        raise Error("cover countermodel replay requires n>=4")
    var tables=build_seed_overlap_tables_screened(member(n))
    var source=labelled(tables,0,1,-n-1,n+4,-2)
    var target=labelled(tables,0,2,-n,n+3,-1)
    if not in_rectangle(n,-n-1,n+4,-2) or in_rectangle(n,-n,n+3,-1):
        raise Error("rectangle countermodel predicate failed")
    _=checked_step(tables,source,0,3,target)
    print("CLASS_A_COVER_ESCAPE",n,"source",0,1,-n-1,n+4,-2,"indices",0,3,"child",0,2,-n,n+3,-1,"source_sum",1,"child_sum",2,"seed_reachability=not_asserted")
