"""Exact loaded Maxwell-material match and reverse cross-band reaction.

Normalized lossless finite Whitney model; no measured material law, source
covariance, or local HF fifth-order constitutive realization is asserted.
"""
import sympy as S
from sympy.polys.matrices import DomainMatrix
from solar_steelman_material_metric import run as metric
from solar_steelman_whitney_lift import solve
from solar_steelman_seven_edge import Dp

I=S.I

def zmat(x):
    return x.applyfunc(S.expand)==S.zeros(*x.shape)


def geometry_obstruction(m):
    d=m['d'];M,G,C,T=d['M'],d['G'],d['C'],d['T'];R=m['R']
    # Exact gradient representation in the enriched material space.
    assert R*G==M*G
    K=C.T*d['N']*C+R-M
    assert G.T*K==S.zeros(G.cols,M.rows)
    # The middle first-edge source has nonzero divergence on middle nodes.
    # Every inner receiver injection has zero divergence there, regardless
    # of its chosen seven-vector. Thus the alpha=w^2=1 forced system has
    # no solution for this fixed nonzero source; not a numerical singularity.
    s=S.eye(15)[:,1]; recv=S.eye(15)[8:15,:]
    div=G.T*T.T
    assert div[6:12,:]*s!=S.zeros(6,1)
    assert div[6:12,:]*recv.T==S.zeros(6,7)
    print('PASS exact alpha=1 half-band charge resonance obstruction',flush=True)


def loaded(m,alpha,w,source,recv):
    d=m['d'];M,N,G,C,D,T=d['M'],d['N'],d['G'],d['C'],d['D'],d['T'];H,B,U,R=m['H'],m['B'],m['U'],m['R']
    K=C.T*N*C+alpha*R-w*w*M
    A=solve(K,T.T);assert K*A==T.T
    X=w*T*A;assert X==X.T
    x=recv*X*source;load=x.dot(x);assert load>0
    # Same fixed source direction as original seven-edge donor. Re-solve
    # compensators from the LOADED impedance; do not reuse bare-shell load.
    p=I*x/load
    block=S.ones(1,1).row_join(-I*x.T).col_join((I*x).row_join(-load*S.eye(7)))
    fwd=solve(block,S.Matrix([2]+[0]*7));assert fwd==S.Matrix([1]).col_join(p)
    ip=source-recv.T*p;f=T.T*ip
    E=I*w*A*ip;b=-C*E/(I*w);z=alpha*U*E/(I*w)
    assert zmat(I*w*M*E-C.T*N*b+B*z-f)
    assert zmat(I*w*b+C*E)
    assert zmat(I*w*H*z/alpha-B.T*E)
    assert zmat(I*w*G.T*M*E-G.T*(f-B*z))
    assert zmat(D*b)
    # Total charge splits external and material; both periodic, no deletion.
    qext=G.T*f/(I*w);qmat=-G.T*B*z/(I*w)
    assert zmat(G.T*M*E-qext-qmat)
    v=T*E;vs=(source.T*v)[0];vr=recv*v
    assert S.expand(vs-I*(source.T*X*source)[0])==1
    assert zmat(vr+I*(recv*X*recv.T)*p-load*p)
    assert S.expand(S.re((p.H*vr)[0]))==1
    assert S.expand(S.re((z.H*B.T*E)[0]))==0
    assert S.expand(S.re((ip.H*v)[0]))==0
    P=Dp.T*(Dp*Dp.T).inv()*Dp
    assert not zmat(P*p) and not zmat((S.eye(7)-P)*p)
    # z is the minimum kinetic representative of its OWN actual material
    # current, not a prescribed receiver injection: H z/alpha=B^T E/(iw).
    assert zmat(H*z/alpha-B.T*E/(I*w))
    print('PASS loaded band',w,'alpha',alpha,'incident=1 useful=1 reflection=0 material work=0',flush=True)
    print('  receiver R',float(load),'material kinetic phasor norm',float(S.re((z.H*H*z/alpha)[0])),'charge norm',float(S.re(((G.T*M*E).H*(G.T*M*E))[0])),flush=True)
    return dict(E=E,b=b,z=z,X=X,p=p,load=load,source=source,recv=recv,v=v)


def rmm(A,B):
    # Exact rational products via common integer denominators. Avoid
    # repeated huge rational gcds in the occupied low-band coefficients.
    da,AA=DomainMatrix.from_Matrix(A).convert_to(S.QQ).clear_denoms(convert=True)
    db,BB=DomainMatrix.from_Matrix(B).convert_to(S.QQ).clear_denoms(convert=True)
    return (AA*BB).to_Matrix()/(da*db).to_sympy()


def pair(v):
    return v.applyfunc(lambda t:S.expand(S.re(t))),v.applyfunc(lambda t:S.expand(S.im(t)))


def bilinear(a,b):
    ar,ai=a;br,bi=b
    return (rmm(ar.T,br)[0]-rmm(ai.T,bi)[0])+I*(rmm(ar.T,bi)[0]+rmm(ai.T,br)[0])


def cross_band_reaction(m,alpha,rows):
    """Replace intermediate terminals within the SAME loaded field geometry.

    Total material state = dynamically responding background + minimum-
    kinetic current increment. Only high source and low final load remain.
    The required force is derived, not assumed supplied by a physical HF law.
    """
    d=m['d'];M,N,G,C,D,T=d['M'],d['N'],d['G'],d['C'],d['D'],d['T'];H,B,U,R=m['H'],m['B'],m['U'],m['R']
    # Invert on port basis first, not on enormous matched-current fractions.
    J=solve(R,T.T);Z=rmm(U,J);HZ=rmm(B.T,J)
    assert rmm(B,Z)==T.T and rmm(H,Z)==HZ
    out=[]
    for n,(w,row) in enumerate(zip((S.Integer(2),S.Integer(1)),rows)):
        source,recv,p=row['source'],row['recv'],row['p'];E,zbg=row['E'],row['z']
        jport=recv.T*p if n==0 else -source
        jr,ji=pair(jport);er,ei=pair(E);zr,zi=pair(zbg)
        ar,ai=rmm(Z,jr),rmm(Z,ji)
        hr,hi=rmm(HZ,jr),rmm(HZ,ji)
        # Exact increments in Maxwell equation: B*za = T^T*jport.
        jr_field,ji_field=rmm(T.T,jr),rmm(T.T,ji)
        assert rmm(B,ar)==jr_field and rmm(B,ai)==ji_field
        # Increment in material equation: reaction = iw H*za/alpha.
        assert rmm(H,ar)==hr and rmm(H,ai)==hi
        rr,ri=-w*hi/alpha,w*hr/alpha
        z=(zr+ar,zi+ai);r=(rr,ri)
        # Loaded equations already checked independently. Replacing external
        # f by f+T^T*jport and material zbg by zbg+za preserves Maxwell,
        # charge continuity and magnetic Gauss coefficientwise.
        field_work=rmm(er.T,jr_field)[0]+rmm(ei.T,ji_field)[0]
        reaction_work=rmm(z[0].T,rr)[0]+rmm(z[1].T,ri)[0]
        assert field_work==(1 if n==0 else -1)
        assert reaction_work==-field_work
        out.append((z,r))
        print('PASS same loaded field band',w,'material work',field_work,'required reaction work',reaction_work,flush=True)
    zhi,rhi=out[0];zlo,rlo=out[1]
    # Real RMS fields with low-band phase h=(1+i)/sqrt2. Retain rational
    # vector coordinates; apply phases only to scalar Fourier coefficients.
    h=(1+I)/S.sqrt(2)
    def neg(a):return a[0],-a[1]
    zs={2:(zhi,1),-2:(neg(zhi),1),1:(zlo,h),-1:(neg(zlo),S.conjugate(h))}
    rs={2:(rhi,1),-2:(neg(rhi),1),1:(rlo,h),-1:(neg(rlo),S.conjugate(h))}
    coeff={k:S.Integer(0) for k in range(-4,5)}
    for k,(z,p) in zs.items():
        for l,(r,q) in rs.items():coeff[k+l]+=p*q*bilinear(z,r)/2
    coeff={k:S.expand(v) for k,v in coeff.items()}
    assert coeff[0]==0
    for k in range(1,5):assert S.expand(coeff[-k]-S.conjugate(coeff[k]))==0
    active=[k for k in range(1,5) if coeff[k]!=0]
    assert active
    # Required conservative auxiliary store: derivative = -z^T r.
    # Periodic primitive and sufficient positive offset are exact; no
    # physical HF mechanism for realizing this store is asserted.
    store={k:S.expand(-coeff[k]/(I*k)) for k in coeff if k}
    assert all(S.expand(I*k*store[k]+coeff[k])==0 for k in store)
    assert all(S.expand(store[-k]-S.conjugate(store[k]))==0 for k in range(1,5))
    bound=2*sum(abs(S.re(store[k]))+abs(S.im(store[k])) for k in range(1,5))
    assert bound>0
    print('PASS same loaded two-band reaction mean=0; nonzero instantaneous harmonics',active,flush=True)
    print('  exact periodic storage derivative and sufficient positive offset; normalized upper offset',float(1+bound),flush=True)
    print('  physical local HF force and store dynamics NOT constructed',flush=True)
    return coeff,store,bound


def run(m=None,stage='all'):
    if m is None:m=metric()
    geometry_obstruction(m)
    # Explicit normalized witness, selected off the exact charge pole.
    # H/alpha is the kinetic metric; alpha is not a fitted physical D.
    alpha=S.Rational(1,2)
    rows=[loaded(m,alpha,S.Integer(2),S.eye(15)[:,0],S.eye(15)[1:8,:]),
          loaded(m,alpha,S.Integer(1),S.eye(15)[:,1],S.eye(15)[8:15,:])]
    if stage in ('all','reaction'):cross_band_reaction(m,alpha,rows)
    print('PASS selected stage',stage,'conditional loaded matching and/or exact inverse reaction',flush=True)

if __name__=='__main__':run()
