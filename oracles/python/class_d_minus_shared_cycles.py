"""Independent integer/Fraction guard and Farkas replay for supplied cycles.

Canonical: kernel/psc/class_d_minus_shared_cycles.mojo. No uniform search.
"""
from fractions import Fraction

NEGATIVE_STATES = [(1,1,-4,7,-5),(1,0,3,-6,4),(1,0,-3,5,-4),
                   (1,2,3,-6,4),(1,1,-3,5,-4),(2,2,2,-6,6)]
NEGATIVE_SEGMENTS = [(0,2),(0,0),(0,1),(0,0),(1,1),(2,0)]


def segment(letter, kind):
    if letter not in range(3) or kind not in range(3):
        raise ValueError("invalid typed segment")
    first = int(letter != 0)
    last = int(letter != 1)
    r = [(3,5,1),(3,6,1),(2,4,1)][letter]
    if kind == 0:
        return first,(0,0),(0,0,0),(0,0,0)
    if kind == 1:
        return 2,(1-first,first),(0,1,0),r
    return last,(1-first,first),(r[0],r[1]+1,r[2]),(r[0],r[1]+1,r[2])


def sub(a,b):
    return tuple(x-y for x,y in zip(a,b))


def shift(form):
    a,c,b = form
    return c+2*a+b,a,b


def cycle_forms(states, segments):
    if not states or len(states)!=len(segments) or len(states)>128:
        raise ValueError("incomplete/over-budget cycle")
    forms = []
    for n,((top,bottom,x,c,y),(kt,kb)) in enumerate(zip(states,segments)):
        if any(abs(z)>1000000 for z in (x,c,y)):
            raise ValueError("state budget exceeded")
        st,sb = segment(top,kt),segment(bottom,kb)
        target = states[(n+1)%len(states)]
        if target[:4] != (st[0],sb[0],x+c+sb[1][0]-st[1][0],x+c+2*y+sb[1][1]-st[1][1]):
            raise ValueError("typed affine edge mismatch")
        req = (-(3*x+3*c+2*y),sum(target[2:])-(7*x+8*c+6*y),-(x+c+y))
        forms.extend([shift(sub(req,sub(sb[2],st[3]))),shift(sub(sub(sb[3],st[2]),req))])
    return forms


def farkas_refutes(forms, multipliers):
    if len(forms)!=len(multipliers) or any(y<0 for y in multipliers):
        return False
    total = [sum(Fraction(y)*f[j] for f,y in zip(forms,multipliers)) for j in range(3)]
    return total[0]<0 and all(x<=0 for x in total[1:])
