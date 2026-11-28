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

def ambient_bounds(m,a,gain=S.Integer(100),Wstar=S.Integer(100)):
    """Conservative exact ambient row-sum bound, valid also on embedded leaf.
    Uses original metric inverses; no orthonormal basis rounding.
    """
    from solar_steelman_boundary_weld import branch
    d=m['d'];M,N,C,B,H=d['M'],d['N'],d['C'],m['B'],m['H']
    T=d['T'];ts=T[:1,:];tr=T[8:15,:];hi,lo=a['rows']
    Ls,Ks=branch(S.Integer(2),S.Integer(1),-hi['X'][:1,:1])
    Lr,Kr=branch(S.Integer(1),S.Integer(2),-lo['X'][8:15,8:15])
    Mi=M.inv();Hi=H.inv()/2;Li=Ls.inv();Lri=Lr.inv()
    inf=lambda X:max(sum(abs_upper(v) for v in X[i,:]) for i in range(X.rows))
    base=max(inf(Mi*C.T*N)+inf(Mi*B)+inf(Mi*ts.T)+inf(Mi*tr.T),
             inf(C),inf(Hi*B.T),inf(Li*ts)+inf(Li)+inf(Li*Ks)+inf(Li),
             inf(Lri*tr)+lo['load']*inf(Lri)+inf(Lri*Kr)+inf(Lri),5)
    n=len(a['models']);low=[];jz=S.zeros(H.rows,1);pz=S.zeros(H.rows,1);je=[];pe=[]
    # sqrt(2)<3/2, |(1+i)/sqrt(2)|=1; bound real waveform by l1 phasors.
    for ids,r,c in a['models']:
        l,_,_=ratio_bounds(c);low.append(l)
        sp=2*sum(k*abs_upper(c[k]) for k in range(1,5))
        f=S.Matrix([S.Rational(3,2)*sum(abs(v[i]) for w in (1,2) for v in r[w]) for i in range(len(ids))])
        fp=2*f
        z=S.Matrix([S.Rational(3,2)*sum(abs(v[j]) for w in (1,2) for v in a['data'][w][0]) for j in ids])
        th=fp+f*sp/l
        jz+=Hi[:,ids].applyfunc(abs_upper)*f/l
        pz+=Hi[:,ids].applyfunc(abs_upper)*th
        je.append(sum(f)+z.dot(f)/l);pe.append(z.dot(th))
    # Original instantaneous face and its subtraction are both bounded;
    # the added current-time delayed launch is bounded independently.
    for j in a['order'][1:]:
        k=a['parent'][j];F=abs(a['flows'][j])
        for row in (k,j):
            for col in (k,j):
                sp=2*sum(t*abs_upper(a['models'][col][2][t]) for t in range(1,5))
                je[row]+=2*(F+gain)/low[col]
                pe[row]+=2*(F+gain)*sp/low[col]
    J=max(base+max(jz),max(je));P=max(max(pz),max(pe))
    rb=delay_bounds(a,gain)
    # core lift sums two store energies and phase differences, each norm 2.
    # fraction derivative adds |S'|/S; phase/anchor rows bounded by degree.
    degree=[0]*n
    for j in a['order'][1:]:degree[j]+=1;degree[a['parent'][j]]+=1
    rotor=4*max(degree)+12
    phase_source=3*inf(Li)*(1+1/(2*Wstar))
    reservoir=4+2/Wstar
    # Extra current-time launch term per receiving/sending store row.
    launch=[0]*n
    for j in a['order'][1:]:
        k=a['parent'][j];f=a['flows'][j];src=k if f>0 else j
        launch[src]+=(abs(f)+gain)*rb['r']/2
    rb['a']=2*J+2*P+phase_source+rb['r']+rotor+reservoir+max(launch)
    return rb

def fixture():
    c={k:S.Integer(0) for k in range(-4,5)}
    c[0]=3;c[1]=c[-1]=1
    assert ratio_bounds(c)==(1,6,16)
    print("PASS ratio bound fixture")

if __name__=="__main__":fixture()
