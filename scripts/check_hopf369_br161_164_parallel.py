#!/usr/bin/env python3
"""BR161-164: exact York quadrupole, atomic residual/Pauli and covariant Bianchi.
Local algebra and analytic bounds, not a nonlinear PDE or empirical receipt."""
import argparse
from itertools import combinations, permutations
import sympy as s
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def york():
    r=s.symbols('r',positive=True);z=s.atan(r)
    fp=-2*(r-z)/r**2;gp=-2*(z-r/(1+r*r))/r**2
    b=(s.diff(fp,r)-fp/r)/r**2;v=-s.diff(fp,r)-fp/r;c=-gp/r
    A=s.simplify(s.diff(v,r)+b*r);C=s.simplify(2*b*r);D=s.simplify(s.diff(c,r)*r)
    V=-2*A*A+6*C*C-2*D*D
    F=-300*z*z-(600*r**8+400*r**6-80*r**4-72*r**2-144)*z/(r**9+r**7)+(12*r*r-72)*z*z/r**8-(300*r**6+100*r**4+12*r*r+72)/(r**8+r**6)
    eq(s.diff(F,r),V/r);eq(s.limit(F,r,0,dir='+'),-Q(2224,3));eq(s.limit(F,r,s.oo),-75*s.pi**2)
    I=Q(2224,3)-75*s.pi**2
    # Machin's identity and alternating arctan bounds: exact rational pi enclosure.
    def atan_partial(q,n):return sum((-1)**k*q**(2*k+1)/Q(2*k+1) for k in range(n))
    l=16*atan_partial(Q(1,5),8)-4*atan_partial(Q(1,239),9)
    u=16*atan_partial(Q(1,5),9)-4*atan_partial(Q(1,239),8)
    assert Q(1113,1000)<Q(2224,3)-75*u*u<Q(2224,3)-75*l*l<Q(1114,1000)
    # Exact source moments and angular factor for Newton Hessian.
    mu=s.symbols('mu',real=True);eq(s.integrate((3*mu*mu-1)*mu*mu/2,(mu,-1,1)),Q(4,15))
    eq(s.integrate(256*s.pi*r*r/(1+r*r)**4,(r,0,s.oo)),8*s.pi**2)
    eq(s.integrate(r**3*s.exp(-r),(r,0,s.oo))/s.integrate(r**2*s.exp(-r),(r,0,s.oo)),3)
    # Conservative nonlinear remainder: normalized admitted G4 example.
    eps=Q(1,2000);kap=K0=s.S.One;p0=Q(1,4);a2=kap**2*K0*eps**2;pi=Q(22,7)
    q=kap*eps**2*(32+2*pi)/4+a2*(32+4*pi/3)/8
    U=16*kap*eps**2+8*a2;G=128*kap*eps**2+48*a2
    L1=2*pi*pi*kap*eps**2+2*pi*pi*a2/3;gp=U+L1/12
    hlo=a2*Q(1113,1000)/20;hhi=a2*Q(1114,1000)/20
    err=3*(7*q*G+7*U*gp)+Q(1,4)*7*q*L1+q*hhi
    terr=2*err+8*q*hhi+kap*8*q*64*eps**2*K0/(K0-64*eps**2)
    assert 7*q<1 and 64*eps**2<min(K0,2*p0) and terr<2*hlo
    print('BR161 normalized example upper tidal difference:',-2*hlo+terr, 'approx',s.N(-2*hlo+terr,12))
    print('PASS BR161 exact IY=2224/3-75*pi^2, rational enclosure (1.113,1.114), original source moments and sufficient nonlinear sign budget')

def atomic():
    from check_hopf369_br154_156_atomic import coulomb
    V,W,_,_=coulomb();I=s.eye(15);p=Q(21,128);d=Q(237,1280);z=Q(111,512);delta=z-d
    Z=(V-p*I)*(V-d*I)/((z-p)*(z-d));eq(Z*Z,Z);assert Z.rank()==1
    Ps=[W**k*Z*(W.T)**k for k in range(3)]
    # The singlet orbit is not an orthogonal basis in general.
    E=s.Matrix.hstack(*(P.columnspace()[0] for P in Ps));assert E.rank()==3
    Qe=E*(E.T*E).inv()*E.T;eq(W*Qe,Qe*W)
    P=(V-d*I)*(V-z*I)/((p-d)*(p-z));eq(P*P,P);eq(P*Qe,s.zeros(15));eq(W*P,P*W)
    for i,j in combinations(range(3),2):eq(Ps[i]*Ps[j],s.zeros(15))
    eq(sum(Ps,s.zeros(15)),Qe)
    for k in range(3):
        R=delta*(Ps[k]-Qe/3);eq(R,W**k*V*(W.T)**k-(p*P+d*(I-P)+delta*Qe/3));eq(s.trace(R.T*R),2*delta**2/3)
        eq(R*R-delta*R/3-2*delta**2*Qe/9,s.zeros(15))
    # Reopen rank-one projectors from the signed residual on the retained support.
    R=delta*(Z-Qe/3);eq(R/delta+Qe/3,Z)
    print('PASS BR162 singlet orbit orthogonal triad, signed rank-one reconstruction and exact residual polynomial')

def pauli():
    r,Z,alpha,f,m=s.symbols('r Z alpha f m',positive=True)
    R=Z**Q(5,2)*r*s.exp(-Z*r/2)/(2*s.sqrt(6))
    eq(s.integrate(r*r*R*R,(r,0,s.oo)),1)
    eq(s.integrate(R*R/r,(r,0,s.oo)),Z**3/24)
    zeta=alpha**2*Z/2*s.integrate(R*R/r,(r,0,s.oo));eq(zeta,alpha**2*Z**4/48)
    a=alpha/f;me=m/s.sqrt(f)
    eq(s.sqrt(f)*me*a**4/(m*alpha**4),f**-4)
    eq(s.sqrt(f)*me*a*a/(m*alpha*alpha),f**-2)
    t,k=s.symbols('t k',real=True);F=1-k*t*t/2
    eq(s.diff(F**-4,t,2).subs(t,0),4*k);eq(s.diff(F**-2,t,2).subs(t,0),2*k)
    print('PASS BR163 hydrogenic Pauli radial coefficient, separate Coulomb/fine-structure radion weights')

def cartan():
    # Independent point-jet oracle: endomorphism-valued forms and the
    # covariant second derivative commutator, including torsion.
    I=range(5);eta=s.diag(-1,1,1,1,1);g=lambda a,b:eta[a,b]
    pairs=list(combinations(I,2)); S=s.Matrix(5,5,lambda a,b:Q((min(a,b)*7+max(a,b)*3)%11-5,7))
    R={ij:eta*s.Matrix(5,5,lambda a,b:g(a,ij[0])*S[b,ij[1]]-g(a,ij[1])*S[b,ij[0]]-g(b,ij[0])*S[a,ij[1]]+g(b,ij[1])*S[a,ij[0]]) for ij in pairs}
    def sign(a):return (-1)**sum(a[i]>a[j] for i in range(len(a)) for j in range(i+1,len(a)))
    def get(F,a):return s.zeros(5) if len(set(a))!=len(a) else sign(a)*F[tuple(sorted(a))]
    H={k:sign(tuple(i for i in I if i not in k)+k)*s.prod(g(i,i) for i in I if i not in k)*R[tuple(i for i in I if i not in k)] for k in combinations(I,3)}
    E={ij:eta*s.Matrix(5,5,lambda a,b:0 if a==b else Q((1 if a<b else -1)*((ij[0]*3+ij[1]*5+min(a,b)*2+max(a,b))%13-6),11)) for ij in pairs}
    F={k:R[k]+E[k] for k in pairs}
    def T(i,j,k):return Q((i+2*j+3*k)%9-4,13)
    for Z in (R,H):
        n=len(next(iter(Z)));J={(a,k):s.Matrix(5,5,lambda i,j:Q((a+sum(k)+i*2+j*3)%11-5,17)) for a in I for k in Z}
        for a in I:
            for k in Z:assert J[a,k].shape==(5,5)
        def action(K,ij,ks):
            M=K[ij];v=get(Z,ks);out=M*v-v*M
            for b,k in enumerate(ks):
                for a in I:out-=M[a,k]*get(Z,ks[:b]+(a,)+ks[b+1:])
            return out
        for inds in combinations(I,n+2):
            def square(K,torsion):
                out=s.zeros(5)
                for i,j in combinations(range(n+2),2):
                    ij=(inds[i],inds[j]);ks=tuple(k for b,k in enumerate(inds) if b not in (i,j));v=action(K,ij,ks)
                    if torsion:v-=sum((T(*ij,a)*J[a,ks] for a in I),s.zeros(5))
                    out+=(-1)**(i+j-1)*v
                return out
            eq(square(R,False),s.zeros(5));eq(square(F,True),square(E,True))
        # Algebraic reference square vanishes on R and its Hodge dual;
        # actual square is linear in connection curvature defect and torsion.
    # Reuse the byte-verified BR143 exact graph; the extended discrepancy
    # factors through the remaining spatial four-form compatibility.
    from check_hopf369_br143_145_parallel import trace
    P,X,Q0,M,D,L,E0,Sc,C,Ct,Z=trace();B=L.col_join(E0)
    Dj=s.Matrix.hstack(*(d*X for d in D));ids=list(Dj.T.rref()[1]);trip=list(combinations(range(1,5),3));N=[];diff=[]
    for i in range(4):
        K=-D[i][ids,:]*L
        U=(-Q0*M[i]*Q0).row_join(-Q0*D[i].T).col_join((-D[i]*Q0).row_join(s.zeros(50)))
        diff.append(U*B-B*K)
        n=s.zeros(10,50);j=trip.index(tuple(k for k in range(1,5) if k!=i+1))
        for a in range(10):n[a,10+10*j+a]=(-1)**i
        N.append(n)
    F=s.Matrix.hstack(*diff);Nj=s.Matrix.hstack(*(n*E0 for n in N))
    assert F.rank()==Nj.rank()==Nj.col_join(F).rank()==10
    T=Nj.T.gauss_jordan_solve(F.T)[0].T;eq(T*Nj,F)
    print('PASS BR164 covariant alternating square for R and *R, exact graph discrepancy; no differentiated torsion in commutator source')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['york','atomic','pauli','cartan'],required=True)
    {'york':york,'atomic':atomic,'pauli':pauli,'cartan':cartan}[p.parse_args().part]()
