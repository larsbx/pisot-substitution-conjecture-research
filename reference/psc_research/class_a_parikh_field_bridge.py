"""Independent integer-polynomial bridge: Parikh labels -> exact cubic shifts.

For the minus class-A words, the normalized lengths in the cubic power basis
are Lx=(-1,d,1), Lc=(-1,0,1), Ly=(0,-1,1).  No analytic/numeric root,
finite-index guess, or tile-length Z-independence is used.
"""
from __future__ import annotations

def parameters(k: int, t: int) -> tuple[int, int, int]:
    if type(k) is not int or type(t) is not int or min(k, t) < 0:
        raise ValueError("minus chamber requires nonnegative integral k,t")
    n=k+t+3
    d=k+2*t+5
    return n,d,n+d

def chi(n: int, d: int) -> tuple[int, int, int]:
    return (2,n-d-1,-n-2)

def parikh_shift(d: int, w: tuple[int,int,int]) -> tuple[int,int,int]:
    p,q,r=w
    return (-p-q,d*p-r,p+q+r)

def decode_parikh_shift(d: int, coeff: tuple[int,int,int]) -> tuple[int,int,int]:
    """Exact inverse of the Parikh length lattice of index d."""
    if type(d) is not int or d<=0:
        raise ValueError("positive minus class-A d required")
    u,v,w=coeff
    numerator=u+v+w
    if numerator%d:
        raise ValueError("cubic shift is not in Parikh length lattice")
    p=numerator//d
    q=-u-p
    r=u+w
    answer=(p,q,r)
    if parikh_shift(d,answer)!=coeff:
        raise AssertionError("inverse formula incorrect")
    return answer

def mul_beta(ch: tuple[int,int,int], a: tuple[int,int,int]) -> tuple[int,int,int]:
    c0,c1,c2=ch
    u,v,w=a
    return (-c0*w,u-c1*w,v-c2*w)

def incidence(n: int,d: int,w: tuple[int,int,int]) -> tuple[int,int,int]:
    p,q,r=w
    return (2*p+q+r,q+r,(n+d)*p+n*q+(n-1)*r)

def prefix_vectors(word: tuple[int,...]) -> tuple[tuple[int,int,int],...]:
    out=[];c=[0,0,0]
    for letter in word:
        out.append(tuple(c));c[letter]+=1
    return tuple(out)

def words(k:int,t:int) -> tuple[tuple[int,...],...]:
    n,d,a=parameters(k,t)
    return ((0,)+(2,)*a+(0,), (1,)+(2,)*n+(0,), (0,)+(2,)*(n-1)+(1,))

def indexed_child(k:int,t:int,label:tuple[int,int,int,int,int],i:int,j:int):
    n,d,_=parameters(k,t)
    ww=words(k,t)
    a,b,p,q,r=label
    if not (0<=a<3 and 0<=b<3 and 0<=i<len(ww[a]) and 0<=j<len(ww[b])):
        raise ValueError("invalid actual occurrence/type")
    top=prefix_vectors(ww[a])[i]
    bottom=prefix_vectors(ww[b])[j]
    moved=incidence(n,d,(p,q,r))
    target=tuple(moved[z]+bottom[z]-top[z] for z in range(3))
    return (ww[a][i],ww[b][j],*target),top,bottom

def verify_field_transport(k:int,t:int,label:tuple[int,int,int,int,int],i:int,j:int):
    n,d,_=parameters(k,t)
    child,top,bottom=indexed_child(k,t,label,i,j)
    base=(label[2],label[3],label[4])
    shifted=parikh_shift(d,base)
    delta=tuple(bottom[z]-top[z] for z in range(3))
    after=parikh_shift(d,child[2:])
    expected=tuple(a+b for a,b in zip(mul_beta(chi(n,d),shifted),parikh_shift(d,delta)))
    if after!=expected:
        raise AssertionError((k,t,label,i,j,child,after,expected))
    return child

def test_all_coefficients():
    """Independent exact identity checks on signed integer combinations."""
    checked=0
    for k in range(13):
        for t in range(9):
            n,d,_=parameters(k,t)
            for p in (-3,-1,0,1,4):
                for q in (-2,0,1):
                    for r in (-4,0,1,3):
                        w=(p,q,r)
                        if parikh_shift(d,incidence(n,d,w))!=mul_beta(chi(n,d),parikh_shift(d,w)):
                            raise AssertionError((k,t,w))
                        checked+=1
    return checked

if __name__=='__main__':
    print({'coefficient_cases':test_all_coefficients()})
