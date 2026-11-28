"""Same-cochain Gauss audit and constraint-preserving reference splitting.
The reference is a finite Galerkin map, NOT a physical light-cone solver.
"""
import sympy as S
from itertools import combinations

def incidence(simplices):
    return [S.Matrix(len(hi),len(lo),lambda i,j:sum((-1)**k for k in range(len(hi[i])) if hi[i][:k]+hi[i][k+1:]==lo[j])) for lo,hi in zip(simplices,simplices[1:])]

def cayley(A,h):
    I=S.eye(A.rows)
    return (I-h*A/2).inv()*(I+h*A/2)

def geometry(d,me,mb):
    d0,d1,d2=map(S.Matrix,d);E=S.diag(*me);B=S.diag(*mb)
    ne,nf=d1.cols,d1.rows
    if d1*d0!=S.zeros(nf,d0.cols) or d2*d1!=S.zeros(d2.rows,ne):raise ValueError('chain')
    if min(me+mb)<=0:raise ValueError('positive metric')
    # Unnormalised electric circulation and magnetic flux.
    A=S.zeros(ne+nf);A[:ne,ne:]=E.inv()*d1.T*B;A[ne:,:ne]=-d1
    G=S.diag(E,B);Q=S.diag(d0.T*E,d2)
    assert Q*A==S.zeros(Q.rows,A.cols) and A.T*G+G*A==S.zeros(A.rows)
    return A,G,Q

def split_audit(d,me,mb,h):
    A,G,Q=geometry(d,me,mb);n=A.rows;T=S.eye(n)
    ne=len(me)
    for i in range(ne):
        for j in range(ne,n):
            if A[i,j]:
                P=S.eye(n);ix=[i,j];C=cayley(A.extract(ix,ix),h)
                for k,a in enumerate(ix):
                    for l,b in enumerate(ix):P[a,b]=C[k,l]
                T=P*T
    R=Q*(T-S.eye(n));U=cayley(A,h)
    assert T.T*G*T==G and Q*U==Q
    K=S.Matrix.hstack(*Q.nullspace());assert K.cols>0
    P=K*(K.T*G*K).inv()*K.T*G
    assert P*P==P and Q*P==S.zeros(Q.rows,n) and P.T*G==G*P
    # Diagnostic only: projection dissipates complementary energy; not a free reset.
    D=(S.eye(n)-P)*T*K
    assert Q*T*K==Q*D
    return dict(split=T,reference=U,metric=G,constraint=Q,physical_basis=K,projection=P,
                signed_split_defect=R,physical_leakage=D,global_midpoint_preserves=True,
                causal_admission=False)

def augmented_step(d,me0,me1,mb,alpha,omega2,gamma,sigma,load,z,jn,jc,h):
    """Rectangular Whitney cochain ADE lift of #1524 endpoint mass identity.
    State E,B,P,V; P,V are dual electric displacement/rate cochains.
    q' = d0^T(Jn+Jc-(sigma+load)E_mid); magnetic divergence preserved.
    """
    d0,d1,d2=map(S.Matrix,d);ne,nf=d1.cols,d1.rows
    E0,E1,M=map(lambda v:S.diag(*v),(me0,me1,mb))
    if min(me0+me1+mb)<=0 or min(alpha,omega2,h)<=0 or min(gamma,sigma,load)<0:raise ValueError('material')
    I=S.eye(ne);n=3*ne+nf;es=slice(0,ne);bs=slice(ne,ne+nf);ps=slice(ne+nf,2*ne+nf);vs=slice(2*ne+nf,n)
    K=S.zeros(n);K[es,bs]=d1.T*M;K[es,es]=-(sigma+load)*I;K[es,vs]=-I
    K[bs,es]=-d1;K[ps,vs]=I;K[vs,es]=alpha*I;K[vs,ps]=-omega2*I;K[vs,vs]=-gamma*I
    M0=S.diag(E0,S.eye(nf),I,I);M1=S.diag(E1,S.eye(nf),I,I)
    F=S.zeros(n,ne);F[es,:]=I
    L=M1-h*K/2;T=L.inv()*(M0+h*K/2);J=L.inv()*h*F
    y=T*z+J*(jn+jc);mid=(z+y)/2;e=mid[es,:];v=mid[vs,:]
    G0=S.diag(E0,M,omega2/alpha*I,I/alpha);G1=S.diag(E1,M,omega2/alpha*I,I/alpha)
    dot=lambda a,b:(a.T*b)[0]
    Wn=h*dot(e,jn);Wc=h*dot(e,jc);Wm=-dot(z[es,:],(E1-E0)*y[es,:])/2
    loss=h*(sigma*dot(e,e)+gamma/alpha*dot(v,v));use=h*load*dot(e,e)
    delta=(dot(y,G1*y)-dot(z,G0*z))/2
    gauss=d0.T*(E1*y[es,:]+y[ps,:]-E0*z[es,:]-z[ps,:])-h*d0.T*(jn+jc-(sigma+load)*e)
    mag=d2*(y[bs,:]-z[bs,:])
    assert S.simplify(delta+loss+use-Wn-Wc-Wm)==0
    assert gauss==S.zeros(d0.cols,1) and mag==S.zeros(d2.rows,1)
    return dict(state=y,T=T,F=J,modulation=Wm,natural=Wn,controller=Wc,loss=loss,useful=use,storage_delta=delta,
                charge_increment=h*d0.T*(jn+jc-(sigma+load)*e),gauss=gauss,magnetic=mag,causal_admission=False)
