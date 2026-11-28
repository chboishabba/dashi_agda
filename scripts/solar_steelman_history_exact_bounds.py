"""Exact harmonic ratio and directed delay coefficient bounds.
Ambient infinity norm; leaf-coordinate transfer requires an independent
basis norm bound. No sampled maximum is used as a certified bound.
"""
import sympy as S
from solar_steelman_combined_static_fibre import modrank

def abs_upper(v):
    v=S.expand(v)
    return abs(S.re(v))+abs(S.im(v))

def ratio_bounds(c):
    low=c[0]-2*sum(abs_upper(c[k]) for k in range(1,5))
    assert low>0
    d1=2*sum(k*abs_upper(c[k]) for k in range(1,5))
    d2=2*sum(k*k*abs_upper(c[k]) for k in range(1,5))
    # R has two energy entries 1/S and two phase entries +/- S'/S.
    r=2*(1+d1)/low
    rp=2*(d1+d2)/low+2*d1*d1/low**2
    # first term for d(1/S) is actually d1/low²; use exact expression.
    rp=2*d1/low**2+2*d2/low+2*d1*d1/low**2
    return low,r,rp

def delay_bounds(a,gain=S.Integer(100)):
    n=len(a['models']);gain=S.Rational(gain)
    rows1=S.zeros(n);rows2=S.zeros(n)
    for j in a['order'][1:]:
        k=a['parent'][j];f=a['flows'][j]
        if f==0:raise ValueError("zero-flow kink requires directional analysis")
        src,dst,F=(k,j,f) if f>0 else (j,k,-f)
        rows1[src,dst]-=(F-gain)/2
        rows1[dst,src]+=(F+gain)/2
        rows2[dst,dst]+=(F-gain)/2
    inf=lambda M:max(sum(abs(v) for v in M[i,:]) for i in range(M.rows))
    rr=[ratio_bounds(c) for _,_,c in a['models']]
    return dict(r=max(x[1] for x in rr),rprime=max(x[2] for x in rr),
                b=inf(rows1),c=inf(rows2),min_store=min(x[0] for x in rr))

def static_leaf(m,a):
    d=m['d'];C,N,B=d['C'],d['N'],m['B']
    # Parameterize magnetic shifts directly in im C, not an arbitrary
    # solution with an unverified magnetic invariant value.
    cols=C.columnspace();U=S.Matrix.hstack(*cols)
    F=[]
    for ids,r,_ in a['models']:
        for w in (1,2):
            for v in r[w]:
                z=S.zeros(B.cols,1)
                for i,j in enumerate(ids):z[j]=v[i]
                F.append(z)
    F=S.Matrix.hstack(*F)
    A=(C.T*N*U).row_join(-B).col_join(S.zeros(F.cols,U.cols).row_join(F.T))
    rank=modrank(A)
    if rank==A.cols:return dict(status="NO_STATIC_SHIFT_IN_SELECTED_CLASS",rank=rank,nullity=0)
    Z=A.nullspace()
    for v in Z:
        assert A*v==S.zeros(A.rows,1)
        b=U*v[:U.cols,:];z=v[U.cols:,:]
        assert C.T*N*b==B*z and F.T*z==S.zeros(F.cols,1)
    return dict(status="STATIC_SHIFT_WITNESSES",rank=A.cols-len(Z),nullity=len(Z),witnesses=Z)
    # This class fixes all other coordinates. It is not an exhaustive
    # classification of constant or periodic tangent solutions.

def fixture():
    c={k:S.Integer(0) for k in range(-4,5)}
    c[0]=3;c[1]=c[-1]=1
    assert ratio_bounds(c)==(1,6,16)
    print("PASS ratio bound fixture")

if __name__=="__main__":fixture()
