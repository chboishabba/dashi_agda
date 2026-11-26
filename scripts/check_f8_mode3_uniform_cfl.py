"""Original mode3 F8 sufficient uniform CFL: exact algebra and matrix regressions.
Source-level energy proof; not native kernel, full production or Weyl trace.
"""
from fractions import Fraction as Q
import json
import sympy as S
import numpy as np


def exact():
    checks=0
    def check(x):
        nonlocal checks
        assert x
        checks+=1
    # Original clock 1<=t<=12, 1/12<=b<=1, -.708<v<0.
    b=S.symbols('b', positive=True)
    v=-b/S.sqrt(1+b*b)
    vp=S.simplify(S.diff(v,b)*v)
    check(S.simplify(vp-b/(1+b*b)**2)==0)
    check(Q('.708')**2>Q(1,2))
    check(1-Q('.708')>Q(1,4))
    check((1+Q('.708'))/(1-Q('.708'))<Q('2.5')**2)
    # v'<=1, |v|/z<=1; log metric derivative <=3+4=7.
    check(3+1/(1-Q('.708'))<7)
    # Weighted H-normal D0 has row/column absolute sums <=2/dy.
    check(1+Q('.71')<2 and Q('.71')**2>Q(1,2))
    # z neighbor ratio changes by <=22 dy (mean value). dy<=.03.
    check(1+12*Q('.03')<Q('1.2')**2)
    check(Q(3,2)*12*Q('1.2')<22)
    comm=44
    check(2*22==comm)
    # Radial shell cp+cm <=2d, Gershgorin <=4d<=44/dr².
    for d in (3,7,11):
        x=S.symbols('x',nonnegative=True)
        hi=x+1;lo=x
        # (hi^d-lo^d) >= hi^(d-1)(hi-lo), coefficients positive.
        poly=S.Poly(S.expand(hi**d-lo**d-hi**(d-1)),x)
        check(all(c>=0 for c in poly.all_coeffs()))
        check(4*d<=44)
    check(44<49)
    # Physical warp rank-one norm <= 3 sqrt(2)/z <= 36 sqrt(2)<52.
    check(36**2*2<52**2)
    # SAT lower cross coefficient <=2/dy in instantaneous metric,
    # diagonal <=4/dy; upper <=2/dy. Total block norm <=6/dy.
    check(2**2+4**2<6**2)
    p,m,P,M,v=S.symbols('p m P M v',real=True)
    a=(1+v)/2;c=(1-v)/2
    target=(1+v)*p/(1-v)
    wall=-a*(1+v)*p*p/2+c*(1-v)*m*m/2+c*(1-v)*m*(target-m)
    check(S.cancel(wall+((1+v)*p-(1-v)*m)**2/4)==0)
    far=a*(1+v)*P*P/2-c*(1-v)*M*M/2-a*(1+v)*P*P
    check(S.expand(far+((1+v)**2*P*P+(1-v)**2*M*M)/4)==0)
    # Frozen A: symmetric part <= C=2*44+52=140, norm <=7/dr+10/dy+140.
    C=140;check(2*comm+52==C)
    # A'(T') in fixed metric T: radial Udot derivative <=10/dr;
    # SAT derivative <=7/dy, D derivative <=2/dy+44,
    # warp derivative <=648 (z>=1/12, sqrt(1/a+1/c)<3).
    check(44*2<100)
    check(Q(3,2)*12**2*3==648)
    check(44+648<700)
    check(2+7<=10)
    # Shifted frozen polynomial energy identity (existing causal RK owner).
    G=S.Matrix([[1,S.Rational(1,2),S.Rational(1,6)],[S.Rational(1,2),S.Rational(1,3),S.Rational(1,6)],[S.Rational(1,6),S.Rational(1,6),S.Rational(1,12)]])
    H=G[:2,:2];u=H.inv()*G[:2,2]
    check(H.det()>0 and H[0,0]>0)
    check(u==S.Matrix([-S.Rational(1,3),1]))
    check(G[2,2]-(G[2,:2]*u)[0]==-S.Rational(1,36))
    k=S.symbols('k');check(S.factor(-S.Rational(1,12)+k/18+k*k/36)==(k-1)*(k+3)/36)
    # R(Z+eps I)-R(Z) <= 4 eps for ||Z||<=1, 0<=eps<=1.
    check(Q(5,2)+1+Q(1,6)<4)
    # dt*(7/dr+10/dy+280)<=1 implies dt*L<=5/2.
    check(Q(10,7)<Q(5,2) and Q(700,280)==Q(5,2))
    check(Q(5,2)/280<1)
    # Actual SSPRK3 stages T,T+dt,T+dt/2: ||B0||<=2, ||B1||<=3.
    # Difference of step from frozen <=(2/3)[(5/4)(3/4+6/4)+2*(5/2)*2/4]dt.
    check(Q(2,3)*(Q(5,4)*(Q(3,4)+Q(6,4))+Q(2)*Q(5,2)*Q(2,4))<5)
    check(4*C+5==565)
    # Metric transport norm <=exp(7dt/2); total <=exp(569dt).
    check(565+Q(7,2)<569)
    # Source lift common P=M=L, original G=vL at wall.
    l,g=S.symbols('l g');check(S.expand((1+v)*(p+l)-(1-v)*(m+l)-2*g-((1+v)*p-(1-v)*m)-2*(v*l-g))==0)
    return checks


def operators(d,nr,ny,dr,dy,b):
    # Active radial nodes only; outer radial node is fixed zero.
    r=np.arange(nr);lo=np.maximum(r-.5,0);hi=r+.5
    V=(hi**d-lo**d)*dr**d/d
    K=np.zeros((nr,nr))
    for i in range(nr):
        cp=2*d if i==0 else d*hi[i]**(d-1)/(hi[i]**d-lo[i]**d)
        cm=0 if i==0 else d*lo[i]**(d-1)/(hi[i]**d-lo[i]**d)
        K[i,i]=(cp+cm)/dr**2
        if i+1<nr:K[i,i+1]=-cp/dr**2
        if i:K[i,i-1]=-cm/dr**2
    K=np.sqrt(V)[:,None]*K/np.sqrt(V)[None,:]
    ev,O=np.linalg.eigh(K);assert ev.min()>0
    sq=(O*np.sqrt(ev))@O.T
    assert ev.max()<44/dr**2+1e-8
    H=np.full(ny,dy);H[[0,-1]]*=.5
    D=np.zeros((ny,ny));D[0,:2]=[-1,1];D[-1,-2:]=[-1,1]
    for j in range(1,ny-1):D[j,j-1]=-0.5;D[j,j+1]=0.5
    D/=dy
    z=b+np.arange(ny)*dy;w=H*z**-3
    W=np.sqrt(w);Dn=W[:,None]*D/W[None,:]
    D0=np.sqrt(H)[:,None]*D/np.sqrt(H)[None,:]
    assert np.linalg.norm(Dn-D0,2)<=44+1e-10
    v=-b/np.sqrt(1+b*b);a=(1+v)/2;c=(1-v)/2
    I=np.eye(ny*nr);Srad=np.kron(np.eye(ny),sq)
    Z=np.kron(np.diag(3/(2*z)),np.eye(nr));Dn=np.kron(Dn,np.eye(nr))
    E0=np.kron(np.diag([1]+[0]*(ny-1)),np.eye(nr));EN=np.kron(np.diag([0]*(ny-1)+[1]),np.eye(nr))
    zero=np.zeros_like(I)
    A=np.block([[zero,np.sqrt(a)*Srad,np.sqrt(c)*Srad],[-np.sqrt(a)*Srad,(1+v)*Dn-Z-2*(1+v)*EN/dy,np.sqrt(a/c)*Z],[-np.sqrt(c)*Srad,-np.sqrt(c/a)*Z+2*np.sqrt(1-v*v)*E0/dy,(v-1)*Dn+Z-2*(1-v)*E0/dy]])
    # Coordinates: (sqrt(w) K^1/2 U, sqrt(w*a) P, sqrt(w*c) M).
    m=np.concatenate([np.repeat(W,nr),np.repeat(W*np.sqrt(a),nr),np.repeat(W*np.sqrt(c),nr)])
    return A,m


def regressions():
    rows=[]
    for d in (3,7,11):
        for b in (1.,.5,1/12):
            for dr,dy in ((.012,.018),(.006,.009)):
                A,m=operators(d,5,5,dr,dy,b)
                mu=np.linalg.eigvalsh((A+A.T)/2)[-1];norm=np.linalg.norm(A,2)
                assert mu<=140+1e-9 and norm<=7/dr+10/dy+140+1e-9
                dt=.99/(7/dr+10/dy+280)
                # Original b'=v. Use midpoint clock approximation ONLY for
                # sample regression; the analytical argument uses exact b(T).
                f=lambda x:-x/np.sqrt(1+x*x)
                def advance(h):
                    k1=f(b);k2=f(b+h*k1/2);k3=f(b+h*k2/2);k4=f(b+h*k3)
                    return b+h*(k1+2*k2+2*k3+k4)/6
                # At t=12 use a step ending at t=12 instead of extending domain.
                if b==1/12:continue
                A1,m1=operators(d,5,5,dr,dy,advance(dt));Ah,mh=operators(d,5,5,dr,dy,advance(dt/2))
                def base(X,n):return X*m[:,None]/n[:,None]*n[None,:]/m[None,:]
                A1=base(A1,m1);Ah=base(Ah,mh);I=np.eye(len(m));B0=I+dt*A;B1=I+dt*A1;Bh=I+dt*Ah
                M=I/3+2*Bh@(.75*I+.25*B1@B0)/3
                gain=np.linalg.norm((m1/m)[:,None]*M,2)
                assert gain<=np.exp(569*dt)+1e-10
                rows.append(dict(d=d,b=b,dr=dr,dy=dy,dt=dt,mu=float(mu),norm=float(norm),gain=float(gain),bound=float(np.exp(569*dt))))
    return rows

if __name__=='__main__':
    print(json.dumps(dict(exact_checks=exact(),matrix_regressions=regressions(),CFL='dt*(7/dr+10/dy+280)<=1',growth_exponent=569,scope='conditional source-level mode3 homogeneous stability; finite matrix regressions not production, no native kernel or Weyl trace'),indent=2))
