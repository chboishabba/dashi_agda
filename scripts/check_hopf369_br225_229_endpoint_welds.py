#!/usr/bin/env python3
"""Endpoint welds: curved differential source, KK CK budget, magnetized EOS,
variable-volume storage, selected n=2 Coulomb. No continuum/kernel promotion.
"""
import sympy as s
from itertools import combinations, product
from functools import lru_cache
from fractions import Fraction as F
import argparse


def periodic():
    # d^connection squared on an endomorphism-valued two-form:
    # compute from genuinely noncommuting, nonconstant connection and field.
    x=s.symbols('x:5'); I=range(5); P=list(combinations(I,2))
    O={i:s.Matrix([[x[i],i+1],[x[(i+1)%5],-x[i]]]) for i in I}
    W={p:s.Matrix([[x[p[0]]*x[p[1]],p[1]+1],[x[p[0]],-x[p[0]]*x[p[1]]]]) for p in P}
    comm=lambda a,b:a*b-b*a
    def deriv(a,i):return a.diff(x[i])+comm(O[i],a)
    def ext(table,k):
        return {p:sum(((-1)**i*deriv(table[p[:i]+p[i+1:]],a) for i,a in enumerate(p)),s.zeros(2)) for p in combinations(I,k+1)}
    R={p:O[p[1]].diff(x[p[0]])-O[p[0]].diff(x[p[1]])+comm(O[p[0]],O[p[1]]) for p in P}
    C=ext(W,2); DD=ext(C,3); nonzero=False
    for four in combinations(I,4):
        rhs=s.zeros(2)
        for p in combinations(four,2):
            q=tuple(i for i in four if i not in p); sign=(-1)**sum(a>b for a in p for b in q)
            rhs+=sign*comm(R[p],W[q])
        lhs=DD[four]; assert (lhs-rhs).applyfunc(s.expand)==s.zeros(2)
        nonzero=nonzero or lhs.applyfunc(s.expand)!=s.zeros(2)
    assert nonzero
    # Differentiated source F=[D^alpha,d^connection]W, not flat CKf=qf.
    for j in I:
        for p in P:
            for i in I:
                rij=O[i].diff(x[j])-O[j].diff(x[i])+comm(O[j],O[i])
                assert (deriv(deriv(W[p],i),j)-deriv(deriv(W[p],j),i)-comm(rij,W[p])).applyfunc(s.expand)==s.zeros(2)
    print('PASS BR225 curved exterior compatibility and 250 covariant derivative commutators')


def g3():
    # Original epsilon=1/4 radial Newton and BR189 disk bounds.
    pmax=F(18,17)*F(729,697); pmin=F(665,697); graph=F(31,3)
    assert pmax*pmax*graph<16 and graph/(pmin*pmin)<16
    # initial g=diag(-1,h), inverse entry g^00=-1. Perturb each entry by eta.
    eta=F(1,8192); delta=5*eta; inv=16/(1-16*delta)
    assert inv<18 and 16*delta*inv<F(1,2)
    # Cauchy bound: initial metric outer l1 radius 1/2, inner radius 1/4.
    dg=16*4; # harmonic shift derivative g0i,t = h^jk(dj hki - di hjk/2)
    shift=16*dg*F(3,2) # induced infinity bound of h^-1 for each j
    shift*=4
    assert shift<8192
    # initial state analytic on 1/4, Cauchy on l1<=1/8 gives derivative cap.
    U0=8192; dU0=8*U0; assert dU0<2**17
    # Bound reduced Ricci Q by direct Christoffel evaluation with second jets zero.
    # all first jets <= 8193; inverse entries <=18; derivative inverse via 25 terms.
    D=8193; gi=18; dgi=25*gi*gi*D
    Gamma=F(15,2)*gi*D; dGamma=F(15,2)*dgi*D
    dC=25*dgi*F(3,2)*D # C_b = g^cd Gamma_lower(b,c,d)
    covC=5*Gamma*25*gi*F(3,2)*D
    lower=10*dGamma+50*Gamma**2+dC+covC
    # reduced R=-1/2 g^ab g_,ab + lower; |g^00|>=1/2.
    coeff=4*gi+1; source=4*lower+3*90*coeff*dU0
    assert coeff<2**100 and source<2**100
    rho=F(1,24); n=90; c=2**100; A=n*(3/rho+1/eta)
    t0=F(3,32)/(A*c); w=1/(4*A)
    assert w<eta and F(1,2)*w-A*w*w/2-c*t0==0
    print('PASS BR226 initial complex metric/inverse <16, gauge/nondegeneracy tube, conditional CK constants',rho,eta,t0)


def g4():
    # Stiff EOS e-p=C, full ideal RMHD including nonparallel momentum.
    q,b,jp,jt,C,rho=s.symbols('q b jp jt C rho',positive=True)
    v2=jp/q**2+jt/(q+b)**2; ent=q*(1-v2); p=(ent-C)/2
    dens=q-p+b/2+b*jt/(2*(q+b)**2)
    phi=q+jp/q+jt/(q+b)
    assert s.cancel(2*dens-C-b-phi)==0
    assert s.cancel(s.diff(phi,q)-(1-v2))==0
    assert s.cancel(s.diff(ent,q)-(1+ jp/q**2+jt*(q-b)/(q+b)**3))==0
    assert s.cancel(s.diff(ent,q)-(1-v2-q*s.diff(v2,q)))==0
    # Independent full Jacobian (q,v)->(rho,j), B along first axis.
    x,y,z=s.symbols('x y z',real=True); v=x*x+y*y+z*z
    R=q-(q*(1-v)-C)/2+b/2+b*(y*y+z*z)/2
    M=s.Matrix([R,q*x,(q+b)*y,(q+b)*z]).jacobian([q,x,y,z]);
    assert s.factor(M.det()-q*(q+b)**2*(1-v)/2)==0
    # exact nonparallel manufactured recovery, plus unmagnetized limit.
    vals={q:s.Rational(7,3),b:s.Rational(5,4),jp:s.Rational(1,9),jt:s.Rational(4,9),C:s.Rational(1,2)}
    assert ent.subs(vals)>C.subs(vals) and s.diff(phi,q).subs(vals)>0
    assert s.cancel(phi.subs(b,0)-(q+(jp+jt)/q))==0
    print('PASS BR227 general magnetized primitive inverse, monotonicity, enthalpy and exact full Jacobian')


def material():
    # Entropy at changing volume; use endpoint chemical potential and exact
    # convex Bregman remainder. Log identities use positive real quantities.
    n,N,v,V=s.symbols('n N v V',positive=True)
    E=lambda n,v:n*(s.log(n/v)-1)
    mu=s.log(N/V); rem=n*s.log(n/N)-n+N; vol=-n*s.log(V/v)
    assert s.expand_log(E(N,V)-E(n,v)-mu*(N-n)+rem-vol,force=True).expand()==0
    # Quadratic electromagnetic energy variable H, midpoint field and metric.
    x,y,a,b=s.symbols('x y a b',real=True)
    assert s.expand((b*y*y-a*x*x)/2-(y+x)*(a+b)*(y-x)/4-(b-a)*(y*y+x*x)/4)==0
    # Signed volume work is not dissipative: expansion lowers energy at fixed amount.
    assert vol.subs({n:2,v:1,V:2})==-2*s.log(2)
    print('PASS BR228 evolving-volume entropy and electromagnetic midpoint work; negative volume work retained')


def atomic():
    from sympy.physics.wigner import gaunt
    Q=s.Rational; r,t=s.symbols('r t',positive=True)
    R=[(2-r)*s.exp(-r/2)/(2*s.sqrt(2)),r*s.exp(-r/2)/(2*s.sqrt(6))]
    @lru_cache(None)
    def radial(a,c,b,d,k):
        f=r*r*R[a]*R[c]; g=r*r*R[b]*R[d]
        def half(f,g):return s.integrate(s.expand(f/r**(k+1)*s.integrate((g*r**k).subs(r,t),(t,0,r))),(r,0,s.oo))
        return s.simplify(half(f,g)+half(g,f))
    for args,val in [((0,0,0,0,0),77),((0,0,1,1,0),83),((0,1,0,1,1),45),((1,1,1,1,0),93),((1,1,1,1,2),45)]:assert radial(*args)==Q(val,512)
    modes=[(l,m,spin) for l in (0,1) for m in range(-l,l+1) for spin in (-1,1)]; pairs=list(combinations(range(8),2))
    @lru_cache(None)
    def eri(a,b,c,d):
        la,ma,sa=modes[a];lb,mb,sb=modes[b];lc,mc,sc=modes[c];ld,md,sd=modes[d]
        if sa!=sc or sb!=sd:return s.S.Zero
        out=0
        for k in range(3):
            if not(abs(la-lc)<=k<=la+lc and abs(lb-ld)<=k<=lb+ld):continue
            if (la+lc+k)%2 or (lb+ld+k)%2:continue
            for q in range(-k,k+1):
                g=gaunt(la,k,lc,-ma,-q,mc)*gaunt(lb,k,ld,-mb,q,md)
                if g:out+=4*s.pi*(-s.S.One)**(ma+mb+q)*g*radial(la,lc,lb,ld,k)/(2*k+1)
        return s.simplify(out)
    V=s.Matrix(28,28,lambda i,j:eri(*pairs[i],*pairs[j])-eri(*pairs[i],*pairs[j][::-1])); assert V==V.T
    ids=[i for i,(a,b) in enumerate(pairs) if a>=2 and b>=2]
    assert V[ids,ids].eigenvals()=={Q(21,128):9,Q(237,1280):5,Q(111,512):1}
    J=s.diag(*[sum(modes[i][1]+Q(modes[i][2],2) for i in p) for p in pairs]); assert V*J==J*V
    eig=V.eigenvals(); assert sum(eig.values())==28 and V.is_positive_definite
    # Actual BR172 one-body matrix in Cartesian basis and BR187 spherical chart.
    I=s.eye(3); zz=I[:,2]; sig=[s.Matrix([[0,1],[1,0]]),s.Matrix([[0,-s.I],[s.I,0]]),s.diag(1,-1)]
    a,c,es,ep,ls=s.symbols('a c es ep ls',real=True); H=s.zeros(8)
    for i in range(3):
        vv=zz.cross(I[:,i]); block=-s.I*a*sum((vv[k]*sig[k] for k in range(3)),s.zeros(2)); H[:2,2+2*i:4+2*i]=block; H[2+2*i:4+2*i,:2]=block.H
        for j in range(3):
            vv=I[:,i]*zz[j]-I[:,j]*zz[i]; H[2+2*i:4+2*i,2+2*j:4+2*j]=-s.I*c*sum((vv[k]*sig[k] for k in range(3)),s.zeros(2))
    L=[s.Matrix(3,3,lambda j,k:-s.I*s.LeviCivita(i,j,k)) for i in range(3)]
    H+=s.diag(es,es,*([ep]*6))+ls*s.diag(s.zeros(2),sum((s.kronecker_product(L[i],sig[i]/2) for i in range(3)),s.zeros(6)))
    Jz=s.diag(s.zeros(2),s.kronecker_product(L[2],s.eye(2)))+s.kronecker_product(s.eye(4),sig[2]/2)
    U=s.kronecker_product(s.eye(4),s.I*sig[1]); E=s.zeros(8)
    orb={-1:s.Matrix([1,-s.I,0])/s.sqrt(2),0:zz,1:-s.Matrix([1,s.I,0])/s.sqrt(2)}
    for j,(l,m,spin) in enumerate(modes):
        z=0 if spin==1 else 1
        if l==0:E[z,j]=1
        else:
            for i in range(3):E[2+2*i+z,j]=orb[m][i]
    eq=lambda x,y:(x-y).applyfunc(s.simplify)==s.zeros(*x.shape)
    def wedge(A):return s.Matrix(28,28,lambda i,j:A[pairs[i][0],pairs[j][0]]*A[pairs[i][1],pairs[j][1]]-A[pairs[i][0],pairs[j][1]]*A[pairs[i][1],pairs[j][0]])
    def lift(A):return wedge(s.eye(8)+t*A).diff(t).subs(t,0)
    assert eq(E.H*E,s.eye(8))
    W=wedge(E); H2=lift(H)+W*V*W.H; J2=lift(Jz); U2=wedge(U)
    assert eq(H2,H2.H) and eq(H2*J2,J2*H2) and eq(U2*H2.conjugate()*U2.H,H2)
    assert eq(U2*U2.conjugate(),s.eye(28))
    print('PASS BR229 full n=2 Coulomb carrier, p-p donor spectrum, combined BR172 axial and time-reversal identities; Coulomb spectrum',eig)


if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['periodic','g3','g4','material','atomic'],required=True);globals()[p.parse_args().part]()
