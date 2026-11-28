#!/usr/bin/env python3
"""BR157-160: p2 angular action, orbit residual, matter frame, G4 leading quadrupole."""
import argparse
import sympy as s
from check_hopf369_br154_156_atomic import coulomb
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def ls():
    V,W,modes,pairs=coulomb(); I=s.eye(15)
    def lift(A):
        return s.Matrix(15,15,lambda i,j:sum(A[pairs[i][k],pairs[j][l]]*int(pairs[i][1-k]==pairs[j][1-l])*(-1)**(k+l) for k in range(2) for l in range(2)))
    Lz=s.diag(*[m for m,sg in modes]); Sz=s.diag(*[Q(sg,2) for m,sg in modes]); Lp=s.zeros(6);Sp=s.zeros(6)
    for j,(m,sg) in enumerate(modes):
        if m<1:Lp[modes.index((m+1,sg)),j]=s.sqrt(2-m*(m+1))
        if sg==-1:Sp[modes.index((m,1)),j]=1
    lz,sz,lp,sp=map(lift,(Lz,Sz,Lp,Sp));lm=lp.T;sm=sp.T
    L2=lz**2+(lp*lm+lm*lp)/2; S2=sz**2+(sp*sm+sm*sp)/2;Jz=lz+sz;Jp=lp+sp;J2=Jz**2+(Jp*Jp.T+Jp.T*Jp)/2
    eq(lp*lm-lm*lp,2*lz);eq(sp*sm-sm*sp,2*sz)
    for M in (lz,sz,lp,sp):eq(V*M,M*V)
    P=S2/2;D=(L2-2*P)/6;Z=I-P-D
    for A,k in ((P,9),(D,5),(Z,1)):eq(A*A,A);eq(A,A.T);assert A.rank()==k
    eq(P*D,s.zeros(15));eq(P*Z,s.zeros(15));eq(D*Z,s.zeros(15))
    eq(V,Q(21,128)*P+Q(237,1280)*D+Q(111,512)*Z)
    SO=lift(Lz*Sz+(Lp*Sp.T+Lp.T*Sp)/2)
    eq(SO*J2,J2*SO);eq(SO*Jz,Jz*SO)
    assert (SO*L2-L2*SO).rank()==12
    J0=(J2-2*I)*(J2-6*I)/12;J1=-J2*(J2-6*I)/8;J2p=J2*(J2-2*I)/24
    for A,k in ((J0,2),(J1,3),(J2p,10)):eq(A*A,A);assert A.rank()==k
    z=s.symbols('z',real=True);x=s.symbols('x'); H=V+z*SO
    for j,A in enumerate((J0,J1,J2p)):
        E=s.Matrix.hstack(*A.columnspace()); R=(E.T*E).inv()*E.T*H*E;eq(E*R,H*E)
        d=2*j+1
        if j==1:
            eq(R,(s.trace(R)/d)*s.eye(d)); poly=x-s.trace(R)/d
        else:
            tr=s.simplify(s.trace(R)/d); tr2=s.simplify(s.trace(R*R)/d); det=(tr**2-tr2)/2
            eq(R*R-tr*R+det*s.eye(R.rows),s.zeros(R.rows)); poly=x*x-tr*x+det
        print('J',j,'reduced polynomial:',s.factor(poly))
    print('PASS BR157 exact LS projectors, physical angular generators and spin-orbit J blocks')

def residual():
    V,W,_,_=coulomb();I=s.eye(15); Vs=[V,W*V*W.T,W**2*V*(W**2).T]; A=sum(Vs,s.zeros(15))/3; R=V-A
    eq(W*A*W.T,A);eq(sum([R,W*R*W.T,W**2*R*(W**2).T],s.zeros(15)),s.zeros(15))
    B=s.Matrix.hstack(*(v-A for v in Vs));print('residual ranks',R.rank(),B.rank(),'norm squared',s.trace(R.T*R),'average spectrum',A.eigenvals())
    E=s.Matrix.hstack(*B.columnspace());P=E*(E.T*E).inv()*E.T
    eq(W*P,P*W);eq(P*R*P,R);eq(P*P,P)
    assert R!=s.zeros(15);assert (V*W-W*V).rank()==2
    for v in Vs:eq(P*(v-A)*P,v-A)
    print('PASS BR158 exact C3 average, signed orbit residual and invariant support projector')

def frames():
    # Selected zero-mode local leading Coulomb model, independent Maxwell;
    # neglect derivative, curvature, Pauli and nuclear/correlation corrections.
    # psi5=f^(1/4) chi_E after fixed reference circle normalization.
    f,m,e5,L=s.symbols('f m e5 L',positive=True)
    eq(f*f**-2*f**Q(1,2)*f**Q(1,2),1)
    eq(f*f**-2*f**Q(1,2),f**Q(-1,2))
    e=e5/s.sqrt(L*f);mass=m/s.sqrt(f);alpha=e**2/(4*s.pi)
    E=mass*alpha**2;eq(E/(E.subs(f,1)),f**Q(-5,2))
    eq(s.sqrt(f)*E/E.subs(f,1),f**-2)
    eq((1/s.sqrt(f))*s.sqrt(f),1)
    ep,p=s.symbols('ep p',positive=True);t=s.symbols('t',real=True);phi=p*(1-Q(56,3)*ep**2*t*t/p**2)
    eq(s.diff((phi/p)**-2,t,2).subs(t,0),Q(224,3)*ep**2/p**2)
    print('PASS BR159 selected bulk/brane clock phase and radion powers, central leading atomic drift')

def quadrupole():
    r=s.symbols('r',positive=True);fp=-2*(r-s.atan(r))/r**2;gp=-2*(s.atan(r)-r/(1+r*r))/r**2
    b=(s.diff(fp,r)-fp/r)/r**2;v=-s.diff(fp,r)-fp/r;c=-gp/r
    A=s.simplify(s.diff(v,r)+b*r);C=s.simplify(2*b*r);D=s.simplify(s.diff(c,r)*r)
    V2=-2*A*A+6*C*C-2*D*D
    eq(s.limit(V2/r**2,r,0),Q(96,25)); print('far coefficient',s.limit(r**4*V2,r,s.oo))
    import mpmath as mp
    vals=[]
    for digits in (40,70):
        with mp.workdps(digits):
            fn=s.lambdify(r,V2/r,'mpmath'); lo=mp.mpf('1e-6');hi=mp.mpf('1e6')
            val=mp.quad(fn,[lo,mp.mpf('.01'),1,10,hi]);vals.append(float(val));print('leading York integral (truncated,',digits,'digits):',mp.nstr(val,25))
    assert abs(vals[0]-vals[1])<1e-10
    print('PASS BR160 near/far leading terms and reproducible leading York quadrupole quadrature (not interval certified)')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['ls','residual','frames','quadrupole'],required=True)
    {'ls':ls,'residual':residual,'frames':frames,'quadrupole':quadrupole}[p.parse_args().part]()
