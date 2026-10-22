from psc.param_poly import qx_const, qx_neg, qx_sub, qx_affine2, tp_norm, tp_key, tp_add, tp_sub, tp_scale, w_add, w_sub
from psc.symbolic_line import SymVertex, _Closure, Eventual
from class_d_plus_positive_b_chambers import _low_wedge, _high_wedge

def main() raises:
    for kind in range(2):
        var line = _low_wedge(1).line() if kind==0 else _high_wedge().line()
        var cl = _Closure(line^,1,Eventual())
        var v = SymVertex(1,0,[qx_const(0),qx_const(kind),qx_const(-1)])
        var wanted = tp_norm([qx_const(-4),qx_affine2(-5,-2,-2),qx_affine2(0,-3,-4)]) if kind==0 else tp_norm([qx_const(-4),qx_affine2(-2,-2,0),qx_affine2(2,1,0)])
        for sa in range(3):
            for sb in range(3):
                var base = w_sub(w_add(cl.line.mw(v.w),cl.prefix(v.bottom,sb)),cl.prefix(v.top,sa))
                var t = cl.line.t_of(base)
                var lo = tp_add(cl.line.ell[cl.letter(v.bottom,sb)],t)
                var hi = tp_sub(t,cl.line.ell[cl.letter(v.top,sa)])
                var rlo = qx_neg(qx_sub(cl.line.run[v.top],qx_const(1))) if sa==1 else qx_const(0)
                var rhi = qx_sub(cl.line.run[v.bottom],qx_const(1)) if sb==1 else qx_const(0)
                var probes = [tp_add(lo,tp_scale(cl.line.ell[2],rhi)),tp_add(hi,tp_scale(cl.line.ell[2],rlo)),tp_add(lo,tp_scale(cl.line.ell[2],rlo)),tp_add(hi,tp_scale(cl.line.ell[2],rhi))]
                for z in range(4):
                    if tp_key(probes[z])==tp_key(wanted):
                        print("QUERY_MATCH",kind,"segments",sa,sb,"probe",z)
