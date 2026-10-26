#!/usr/bin/env python3
"""Independent Griess1990 -> native rational Albert certificate verifier.

Reuses original source *formula* from Agda #1249
scripts/check_27_origin_albert_griess_product_cut.py, and the actual
Lean RationalAlbertNative Jordan coordinate convention. Unlike Lean #52's
certificate producer this script only READS an external 27x27 map; it does
not run the three-space triality recovery algorithm.

Original mathematical owner: R. L. Griess Jr., J. Algebra 131 (1990),
281-293, DOI 10.1016/0021-8693(90)90176-O.
Exact rational Python verification != Agda or Lean kernel proof.
"""
from itertools import product
from fractions import Fraction as F
import json,sys
import sympy as s

V=list(product(range(3),repeat=3));origin=(0,0,0)
neg=lambda x:tuple((-a)%3 for a in x)
add=lambda x,y:tuple((a+b)%3 for a,b in zip(x,y))
reps=[x for x in V if x!=origin and x<neg(x)]
assert len(reps)==13
Z=(F(0),F(0));unit=(F(1),F(0))
omega=(unit,(F(0),F(1)),(F(-1),F(-1)))
qadd=lambda a,b:(a[0]+b[0],a[1]+b[1])
qmul=lambda a,b:(a[0]*b[0]-a[1]*b[1],a[0]*b[1]+a[1]*b[0]-a[1]*b[1])
def dependent(x,y):
    return x==origin or any(all((k*a-b)%3==0 for a,b in zip(x,y)) for k in range(3))
def phase(x,y):
    a,b,c=x;p,q,r=y
    return (-a*b*r-c*p*q+b*c*p+a*q*r)%3
def coeff(x,y):
    scale=F(1) if dependent(x,y) else F(-1,2)
    return tuple(scale*u for u in omega[phase(x,y)])
def srcprod(x,y):
    out={}
    for a,u in x.items():
        for b,v in y.items():
            z=add(a,b)
            out[z]=qadd(out.get(z,Z),qmul(qmul(u,v),coeff(a,b)))
    return {k:v for k,v in out.items() if v!=Z}
basis=[{origin:unit}]
for a in reps:basis.extend(({a:unit,neg(a):unit},
                            {a:omega[1],neg(a):omega[2]}))
def source_coords(v):
    out=[v.get(origin,Z)[0]]
    assert v.get(origin,Z)[1]==0
    for a in reps:
        x=v.get(a,Z); y=v.get(neg(a),Z)
        assert y==(x[0]-x[1],-x[1]),(a,x,y)
        out.extend(x)
    return s.Matrix(out)
for i,b in enumerate(basis):assert source_coords(b)==s.eye(27)[:,i]

# Independent native coordinate formula: (d0,d1,d2, off12,off20,off01).
def quat(a,b):
    x,y,z,t=a;u,v,w,r=b
    return(x*u-y*v-z*w-t*r,x*v+y*u+z*r-t*w,
           x*w-y*r+z*u+t*v,x*r+y*w-z*v+t*u)
def qc(a):return(a[0],-a[1],-a[2],-a[3])
def plus(a,b):return tuple(u+v for u,v in zip(a,b))
def minus(a,b):return tuple(u-v for u,v in zip(a,b))
def om(a,b):
    x,y=a[:4],a[4:];u,v=b[:4],b[4:]
    return minus(quat(x,u),quat(qc(v),y))+plus(quat(v,x),quat(y,qc(u)))
def oc(a):return qc(a[:4])+tuple(-t for t in a[4:])
def scale(t,a):return tuple(t*u for u in a)
def summed(*vs):return tuple(map(sum,zip(*vs)))
def half(*vs):return scale(F(1,2),summed(*vs))
def inner(a,b):return om(a,oc(b))[0]
def native(A,B):
    a,b,c=A[:3];d,e,f=B[:3]
    x,y,z=A[3:11],A[11:19],A[19:27]
    u,v,w=B[3:11],B[11:19],B[19:27]
    return s.Matrix((
        a*d+inner(z,w)+inner(y,v),
        b*e+inner(z,w)+inner(x,u),
        c*f+inner(y,v)+inner(x,u),
        *half(om(oc(z),oc(v)),scale(b,u),scale(f,x),
              om(oc(w),oc(y)),scale(e,x),scale(c,u)),
        *half(scale(d,y),om(oc(x),oc(w)),scale(c,v),
              scale(a,v),om(oc(u),oc(z)),scale(f,y)),
        *half(scale(a,w),scale(e,z),om(oc(y),oc(u)),
              scale(d,z),scale(b,w),om(oc(v),oc(x)))))

def verify(path):
    data=json.load(open(path))
    assert data['native_coordinate_order'].startswith('diagonal0')
    key='full_27_by_27_native_rational_transport'
    if key not in data:key='native_27x27_map'
    M=s.Matrix([[s.Rational(q) for q in row] for row in data[key]])
    assert M.shape==(27,27) and M.det()!=0
    N=s.Matrix([[s.Rational(q) for q in row] for row in
        data['explicit_native_to_source_inverse']]) if (
            'explicit_native_to_source_inverse' in data) else M.inv()
    assert M*N==s.eye(27) and N*M==s.eye(27)
    nativeGram=s.diag(*([F(1)]*3+[F(2)]*24))
    sourceGram=s.diag(F(3),*sum(([F(6),F(6)] for _ in reps),[]))
    for k in range(13):
        sourceGram[1+2*k,2+2*k]=sourceGram[2+2*k,1+2*k]=-3
    assert M.T*nativeGram*M==sourceGram
    assert M[:,0]==s.Matrix([1,1,1]+[0]*24)
    for i,j in product(range(27),repeat=2):
        lhs=M*source_coords(srcprod(basis[i],basis[j]))
        rhs=native(M[:,i],M[:,j])
        assert lhs==rhs,('Jordan product',i,j,lhs-rhs)
    # Source-selected actual A=(Z/3)^3 rational actor: three genuine
    # Griess character generators. Rather than recompute thousands of
    # target octonion products, check 3×729 SOURCE basis identities; the
    # already-verified Jordan isomorphism transports them to native.
    baseProducts=[[source_coords(srcprod(basis[i],basis[j]))
        for j in range(27)] for i in range(27)]
    phaseR=s.Matrix([[0,-1],[1,-1]])
    for h in range(3):
        T=s.eye(27)
        for k,a in enumerate(reps):
            T[1+2*k:3+2*k,1+2*k:3+2*k]=phaseR**a[h]
        assert T**3==s.eye(27) and T[:,0]==s.eye(27)[:,0]
        for i,j in product(range(27),repeat=2):
            lhs=T*baseProducts[i][j]
            xs=[(k,T[k,i]) for k in range(27) if T[k,i]!=0]
            ys=[(k,T[k,j]) for k in range(27) if T[k,j]!=0]
            rhs=s.zeros(27,1)
            for k,a in xs:
                for l,b in ys:
                    rhs+=a*b*baseProducts[k][l]
            assert lhs==rhs,(h,i,j)
    # Actual adversarial certificate test; no blank success receipts.
    altered=M.copy();altered[0,1]+=1
    assert altered.T*nativeGram*altered!=sourceGram
    print('PASS 3x729 actual source A-character product identities and adversarial matrix mutation')
    print('PASS independent Griess1990 -> native rational Albert certificate')
    print('PASS 729/729 products, invertibility, unit and 27D trace Gram')
    print('UNPAID Agda/Lean kernel and all Monster/KK/physical intertwiners')

if __name__=='__main__':
    if len(sys.argv)!=2:raise SystemExit('usage: checker.py certificate.json')
    verify(sys.argv[1])
