#!/usr/bin/env python3
"""BR175-177: full reference bulk/shape parity split, paired traces, radial inverse.
Exact finite matrices and analytic moment identities; not curved IBVP acceptance."""
import argparse
from itertools import combinations
import sympy as s
Q=s.Rational

def eq(a,b):
    if isinstance(a,s.MatrixBase): assert (a-b).applyfunc(s.simplify)==s.zeros(*a.shape)
    else: assert s.simplify(a-b)==0

def geometry():
    from check_hopf369_br_curvature_energy import carrier,P,Q as pairs
    C,V,X,G,Y,H,J,A,B,R,W,m=carrier()
    F=V.gauss_jordan_solve(s.diag(*[(-1)**(int(4 in P[a])+int(4 in P[b])) for a,b in pairs])*V)[0]
    I=s.eye(35);Ep=(I+F)/2;Em=(I-F)/2;S=G*A[3]
    eq(F**2,I);eq(F.T*G*F,G);eq(F*J,J);eq(R*F,-R)
    for i in range(3):eq(F*A[i],A[i]*F)
    eq(F*A[3],-A[3]*F);assert Ep.rank()==19 and Em.rank()==16
    eq(Ep.T*S*Ep,s.zeros(35));eq(Em.T*S*Em,s.zeros(35));eq(S*J,3*R.T*H)
    # Full jump of reflected fields u=a+b, v=a-b, original minus=Fv.
    a=s.Matrix(s.symbols('a:35'));b=s.Matrix(s.symbols('b:35'));m=s.Matrix(s.symbols('m:9'));j=s.symbols('j',real=True)
    up=a+b;down=F*(a-b)
    eq(up-down,2*Em*a+2*Ep*b);eq(R*(up+down)/2,R*b)
    # On the odd-reflection sector substitute prescribed even component.
    bw=Em*b+j*J*m/2
    eq((bw.T*S*bw)[0]/2,3*j*(m.T*H*R*b)[0]/2)
    for bmat in B:eq(H*bmat,bmat.T*H)
    print('PASS BR175 complete frozen bulk/shape reflection split, retained shape and signed energy cancellation')
    return P,X,G,J,A,R,F

def paired():
    from check_hopf369_br143_145_parallel import trace
    P,X,G,J,A,R,F=geometry();_,X2,Q0,M,D,L,E,Sc,T,Tsp,Z=trace();eq(X,X2)
    Dj=s.Matrix.hstack(*(d*X for d in D));ids=list(Dj.T.rref()[1]);D1=D[0][ids,:]*X;Dn=D[3][ids,:]*X
    Mag=s.zeros(12,100)
    for row,(a,i,j) in enumerate((a,i,j) for a in range(4) for i,j in combinations(range(1,4),2)):Mag[row,10*P.index((i,j))+P.index((a,4))]=-1
    eq(Mag*X*F,-Mag*X)
    u=s.symbols('u',real=True);co=(1-u*u)/(1+u*u);si=2*u/(1+u*u);O=s.eye(5);O[1,1]=O[4,4]=co;O[4,1]=si;O[1,4]=-si
    P2=s.Matrix(10,10,lambda i,j:O[P[i][0],P[j][0]]*O[P[i][1],P[j][1]]-O[P[i][0],P[j][1]]*O[P[i][1],P[j][0]])
    rot=G.inv()*X.T*s.kronecker_product(P2,P2)*X
    for mu,entries,target in ((Q(1,2),{2:1,18:1},s.Matrix([0,0,co/2,0,0,0,-co/2,0,0])),(0,{0:-1,4:1},s.Matrix([0,-co**2,0,co**2,0,0,0,0,0]))):
        w0=s.zeros(35,1)
        for i,v in entries.items():w0[i]=v
        w=(rot*w0).applyfunc(s.factor);eq(F*w,w.subs(u,-u));eq((co*A[0]+si*A[3])*w,mu*w)
        eq(w.T*G*w,w0.T*G*w0)
        c=((co*D1+si*Dn)*w).applyfunc(s.factor);cp=c+c.subs(u,-u);wp=w+F*w
        eq(R*wp,s.zeros(9,1));eq(Mag*X*wp,s.zeros(12,1));eq(Mag*L*cp,s.zeros(12,1))
        eq(Tsp*c,target);eq(Tsp*cp,2*target)
        assert target.subs(u,0)!=s.zeros(9,1)
    print('PASS BR176 paired half-speed and stationary modes satisfy reference wall and magnetic constraints but retain unsuppressed spatial trace')

def radial():
    r,lam,m=s.symbols('r lam m',positive=True);e=s.symbols('e',real=True);D=1+r*r
    W=r**4*s.exp(-lam*r)/D**3
    eq(s.diff(W,lam),-r*W);eq(s.integrate(r**4/D**3,(r,0,s.oo)),3*s.pi/16)
    eq(s.diff(r**5*s.exp(-lam*r)/D**3,r),W*(5-lam*r-6*r*r/D))
    # Moment algebra, positivity strict by non-point-supported weight.
    I0,I1,I2,I3=s.symbols('I0 I1 I2 I3',positive=True)
    f=I1/I0;df=-I1*s.diff(f,I0)-I2*s.diff(f,I1)
    eq(df,-(I0*I2-I1**2)/I0**2)
    t,v=s.symbols('t v',real=True);eq((t-v)**2,t*t+v*v-2*t*v)
    a=e*lam**5*I1/(12*m);c=e*lam**5*I0/(12*m)
    eq(a/c,f);eq(c*12*m/(lam**5*I0),e)
    # large lambda dominated-convergence limiting moments after r=x/lambda
    x=s.symbols('x',positive=True);eq(s.integrate(x**5*s.exp(-x),(x,0,s.oo))/s.integrate(x**4*s.exp(-x),(x,0,s.oo)),5)
    # Degenerate spectral norm with known radial scale.
    eq(a*a+c*c,e*e*lam**10*(I0**2+I1**2)/(144*m*m))
    print('PASS BR177 actual BR170 moment ratio derivative, exact endpoints ingredients and amplitude reconstruction')

if __name__=='__main__':
    p=argparse.ArgumentParser();p.add_argument('--part',choices=['split','paired','radial'],required=True)
    {'split':geometry,'paired':paired,'radial':radial}[p.parse_args().part]()
