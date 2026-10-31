"""Independent exact native Perron vector and Parikh lattice calibration.

For minus class-A k,t>=0, n=k+t+3,d=k+2t+5,A=n+d.
The canonical native Perron vector is the positive cross product of the
first two rows of M^T - beta I, not the beta(beta-1)-normalized research
vector. Integer polynomial arithmetic only, no Perron approximation.
"""

def params(k,t):
    if any(type(x) is not int or x<0 for x in (k,t)):
        raise ValueError('minus class-A integer chamber')
    n=k+t+3; d=k+2*t+5
    return n,d,n+d

def chi(n,d):return (2,n-d-1,-(n+2))

def plus(x,y):return tuple(a+b for a,b in zip(x,y))
def neg(x):return tuple(-a for a in x)
def minus(x,y):return plus(x,neg(y))
def beta_times(x,n,d):
    c0,c1,c2=chi(n,d)
    a,b,c=x
    return (-c0*c,a-c1*c,b-c2*c)

def mul(x,y,n,d):
    out=(0,0,0)
    bx=x
    for z in y:
        out=plus(out,tuple(z*v for v in bx))
        bx=beta_times(bx,n,d)
    return out

def normalized_lengths(n,d):
    return ((-1,d,1),(-1,0,1),(0,-1,1))

def native_lengths(n,d):
    A=n+d
    return ((-A,A,0),(d-n,n,0),(2,-3,1))

def native_scale(n,d):return (n-d,-n-2,1)

def actual_cross_product(n,d):
    A=n+d
    a=((2,-1,0),(0,0,0),(A,0,0))
    b=((1,0,0),(1,-1,0),(n,0,0))
    return (
        minus(mul(a[1],b[2],n,d),mul(a[2],b[1],n,d)),
        minus(mul(a[2],b[0],n,d),mul(a[0],b[2],n,d)),
        minus(mul(a[0],b[1],n,d),mul(a[1],b[0],n,d)),
    )

def normalize(n,d):
    if n<3 or d<5 or d-n-2<0 or 2*n-d-1<0:
        raise ValueError('off-chamber normalized parameter')
    native=native_lengths(n,d)
    canonical=normalized_lengths(n,d)
    lam=native_scale(n,d)
    if actual_cross_product(n,d)!=native:
        raise AssertionError('native eigenvector construction altered')
    if tuple(mul(lam,l,n,d) for l in canonical)!=native:
        raise AssertionError('native scalar ratio not exact')
    for l in native:
        if beta_times(l,n,d)!=matrix_apply(n,d,native)[native.index(l)]:
            raise AssertionError('eigenvector action mismatch')
    return native

def matrix_apply(n,d,lengths):
    A=n+d
    # (left eigenvector) * incidence matrix, columns x/c/y
    return (plus(plus(tuple(2*z for z in lengths[0]),tuple(A*z for z in lengths[2])),(0,0,0)),
            plus(plus(lengths[0],lengths[1]),tuple(n*z for z in lengths[2])),
            plus(plus(lengths[0],lengths[1]),tuple((n-1)*z for z in lengths[2])))

def native_shift(n,d,p,q,r):
    A=n+d
    return (-A*p+(d-n)*q+2*r,A*p+n*q-3*r,r)

def decode_native(n,d,coeff):
    normalize(n,d)
    u,v,w=coeff; A=n+d
    if (u+v+w)%d:raise ValueError('not in native Parikh sublattice')
    q=(u+v+w)//d
    if (v-n*q+3*w)%A:raise ValueError('not in native Parikh sublattice')
    p=(v-n*q+3*w)//A
    r=w
    if native_shift(n,d,p,q,r)!=coeff:raise AssertionError('inverse failed')
    return p,q,r

def incidence(n,d,w):
    p,q,r=w
    return (2*p+q+r,q+r,(n+d)*p+n*q+(n-1)*r)

def words(k,t):
    n,d,A=params(k,t)
    return ((0,)+(2,)*A+(0,), (1,)+(2,)*n+(0,), (0,)+(2,)*(n-1)+(1,))

def prefix(word,i):
    if i<0 or i>=len(word):raise ValueError('missing literal occurrence')
    out=[0,0,0]
    for x in word[:i]:out[x]+=1
    return tuple(out)

def indexed(k,t,w,i,j):
    n,d,A=params(k,t)
    sigma=words(k,t)
    a,b,p,q,r=w
    if not 0<=a<3 or not 0<=b<3:raise ValueError('invalid tile')
    top=prefix(sigma[a],i)
    bot=prefix(sigma[b],j)
    parikh=incidence(n,d,(p,q,r))
    child=tuple(parikh[z]+bot[z]-top[z] for z in range(3))
    lhs=native_shift(n,d,*child)
    rhs=plus(beta_times(native_shift(n,d,p,q,r),n,d),native_shift(n,d,*(bot[z]-top[z] for z in range(3))))
    if lhs!=rhs:raise AssertionError('noncommuting native child')
    return (sigma[a][i],sigma[b][j],*child),lhs
