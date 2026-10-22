"""Scoped class-D assembly; receipts are inputs, never a replacement for proof.

The provenance wrapper binds each receipt to immutable source bytes. This
module checks the exact cover identities and requires both complete native
aggregates. Full CI acceptance is a separate open ledger dependency.
"""
from psc.param_poly import QX, qx_affine2, qx_const, qx_add, qx_sub, qx_scale, qx_is_zero
from finite_linear_algebra.scalar import q_int


def _equal(x: QX, y: QX) raises:
    if not qx_is_zero(qx_sub(x,y)):
        raise Error("class-D cover identity failed")


def verify_class_d_cover() raises:
    # Polynomial identities, not a finite grid. a,b are arbitrary integers.
    for s in [-1,1]:
        var p = qx_affine2(4-s,3,1)
        var q = qx_affine2(4-2*s,3,1)
        var r = qx_affine2(2-2*s,2,1)
        _equal(qx_sub(p,q),qx_const(s))
        _equal(qx_sub(qx_sub(q,r),qx_const(2)),qx_affine2(0,1,0))
        _equal(qx_add(qx_sub(qx_scale(r,q_int(3)),qx_scale(q,q_int(2))),qx_const(2*s+2)),qx_affine2(0,0,1))
        # chi(-1)=2q-2s-3r-3=-b-1. The Pisot hypothesis and
        # integrality imply b>=0 when d=q-r>=2; no residues are lost.
        _equal(qx_sub(qx_sub(qx_scale(q,q_int(2)),qx_scale(r,q_int(3))),qx_const(2*s+3)),qx_affine2(-1,0,-1))
    # Integer lattice determinant of the (q,r) directions is 3*1-1*2=1.
    _equal(qx_const(3*1-1*2),qx_const(1))
    # The five low sectors have adjacent slopes k,k+1. Interfaces j=1..6
    # and high c=5a+7+v join without a lattice gap. In each low sector
    # a=u+v,c=k*u+(k+1)*v with determinant one.
    for k in range(5):
        var a = qx_affine2(0,1,1)
        var c = qx_affine2(0,k,k+1)
        _equal(qx_sub(qx_scale(a,q_int(k+1)),c),qx_affine2(0,1,0))
        _equal(qx_sub(c,qx_scale(a,q_int(k))),qx_affine2(0,0,1))
    # Positive b uses c=b-1, so (a,b)=(0,1) is included.
    _equal(qx_add(qx_affine2(-1,0,1),qx_const(1)),qx_affine2(0,0,1))


def _once(text: String, receipt: String) raises:
    var count = 0
    for line in text.split("\n"):
        if String(line) == receipt:
            count += 1
    if count != 1:
        raise Error("missing or duplicated complete component receipt: " + receipt)


def verify_class_d_receipts(plus: String, minus: String) raises:
    _once(plus,"CLASS_D_PLUS_POSITIVE_B_CHAMBERS_CERTIFIED wedges= 6 explicit_lines= 6 boundary_lines= 73 finite_prefix_pip= 952 max_symbolic_vertices= 164")
    _once(minus,"MINUS_B0_COMPONENT_CERTIFIED a>=0 145 781 4")
    _once(minus,"MINUS_STRIP_CERTIFIED 0 n=b-1 threshold 42 vertices 140 finite_pip 42 crosschecks 42 47")
    _once(minus,"MINUS_STRIP_CERTIFIED 1 n=b-1 threshold 72 vertices 137 finite_pip 72 crosschecks 72 77")
    _once(minus,"MINUS_BOUNDARY_STRIPS_CERTIFIED strips=2 a=0,1 b>=1")
    _once(minus,"MINUS_SEED_COVER_COUNTS 145 9 3 2 1287 12255 1218 9034 2003")
    _once(minus,"MINUS_SEED_COVER_CERTIFIED a>=2 b>=1 all_real_seed_descendants_in_carrier=true abs_sum<=1 parameter_cap=none")
    _once(minus,"MINUS_CORE_BH_CERTIFIED a>=2 b>=1 rank 4")
    _once(minus,"CLASS_D_MINUS_RESIDUAL_BH_CERTIFIED a>=0 b>=0 components=4 universal_139=open")
    # Native source emits these after all mathematical checks; provenance,
    # process exit status and unchanged hypotheses are checked independently.
    verify_class_d_cover()
