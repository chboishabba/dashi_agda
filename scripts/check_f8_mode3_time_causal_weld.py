"""Original F8 mode3 time-graph and causal geometry weld.
Exact SymPy/Fraction algebra; no native kernel or full source-on production.
"""
import json
from fractions import Fraction as Q
from math import isqrt
import sympy as S


def check():
    n=0
    def eq(a,b=0):
        nonlocal n
        assert S.simplify(a-b)==0,(a,b)
        n+=1
    v,vd,vdd,z,G,Gd,chi,dchi,dp,dm,kU,p,m=S.symbols('v vd vdd z G Gd chi dchi dp dm kU p m',real=True)
    a,c=1+v,1-v
    s=a*c
    # Transformed variables p=aP, m=cM; zero-rate lift p=G chi, m=-G chi.
    P,M=p/a,m/c
    W,F=(p+m)/2,(p-m)/2
    eq((a*P+c*M)/2,W);eq((a*P-c*M)/2,F)
    eq((P-M)/2,(F-v*W)/s)
    # Original SAT: m row, after scaling, is 2c(p-m-2G)/dy.
    h=S.symbols('h',positive=True)
    target=(a*P-2*G)/c
    eq(c*2*c*(target-M)/h,2*c*(p-m-2*G)/h)
    eq((p+m).subs({p:G*chi,m:-G*chi}),0)
    eq((p-m-2*G).subs({p:G,m:-G}),0)
    # Clock-dependent principal row scaling; symbolic normal and radial
    # operators are independent indeterminates, and SAT included in L.
    D,K,E0,EN=S.symbols('D K E0 EN',real=True)
    A0=S.Matrix([[0,S.Rational(1,2),S.Rational(1,2)],[-a*K,a*(D-2*EN/h),0],[-c*K,2*c*E0/h,-c*(D+2*E0/h)]])
    R=S.Matrix([[0,0,0],[0,vd/a-3/(2*z),3*a/(2*z*c)],[0,-3*c/(2*z*a),-vd/c+3/(2*z)]])
    B=S.diag(0,vd/a,-vd/c)
    d=lambda x:S.diff(x,v)*vd+S.diff(x,vd)*vdd+S.diff(x,z)*v
    for x in A0.applyfunc(d)-B*A0:eq(x)
    C=R.applyfunc(d)-B*R
    assert not (set().union(*(x.free_symbols for x in C)) & {D,K,E0,EN,h})
    n+=1
    for x in ((A0+R).applyfunc(d)-B*(A0+R)-C):eq(x)
    # First and second time derivative graph algebra, noncommuting.
    A,B,C,Bd,Cd,Y,Y1,Y2,g,gd=S.symbols('A B C Bd Cd Y Y1 Y2 g gd',commutative=False)
    # Y2=(A+B)Y1+C Y+g. Substitute without commuting factors.
    lhs=(A+B)*Y2+(B*A+2*C+Bd)*Y1+Cd*Y+gd
    rhs=(A+2*B)*Y2+(2*C+Bd-B*B)*Y1+(Cd-B*C)*Y+gd-B*g
    eq(S.expand(lhs-rhs).subs(Y2,(A+B)*Y1+C*Y+g).expand())
    # Exact RK time sum: no hidden endpoint half-weight on flat support.
    x=S.symbols('x:9');w=S.symbols('w:9');
    eq(S.expand(sum(w[i]*(x[i+1]-x[i-1]) for i in range(1,8))+sum(x[i]*(w[i+1]-w[i-1]) for i in range(1,8))).subs({w[0]:0,w[1]:0,w[7]:0,w[8]:0}))
    # On-shell normal jet reconstruction, retain arbitrary off-shell defects.
    b,v,vd,W,Wd,G,Gd,L,Uy,Uty,Uyy=S.symbols('b v vd W Wd G Gd L Uy Uty Uyy',real=True)
    s=1-v*v
    q=(G-v*W)/s
    qt=(Gd-vd*W-v*Wd+2*v*vd*q)/s
    yy=(Wd-2*v*qt-(vd-3/b)*q-L)/s
    eq(v*W+s*q,G)
    eq(vd*W+v*Wd-2*v*vd*q+s*qt,Gd)
    eq(-Wd+2*v*qt+s*yy+(vd-3/b)*q+L)
    # Exact signed original lower-wall stencil corrections (any state).
    a,c,h=S.symbols('a c h',nonzero=True);P0,P1,M0,M1,U0,U1,U2,Fb,SAT=S.symbols('P0 P1 M0 M1 U0 U1 U2 Fb SAT')
    N0,N1=(P0-M0)/2,(P1-M1)/2
    Q0=N0-(U1-U0)/h;Qdot=-SAT/2
    Pt=a*(P1-P0)/h+Fb;Mt=-c*(M1-M0)/h+Fb+SAT
    dy2=(U2-2*U1+U0)/h**2;dy1=(-3*U0+4*U1-U2)/(2*h)
    interior={U2:U0+2*h*N1}
    eq((dy1+2*Q0+N1-N0-N0).subs(interior))
    eq((dy2/2-Q0/h-Qdot/c-((Pt-Fb)/(2*a)+(Mt-Fb)/(2*c))).subs(interior))
    # With exact interior Qdot=0, the same correction commutes with
    # semidiscrete time differentiation (not a raw time-difference claim).
    W0,W1,W2,N0t,N1t,Q0t=S.symbols('W0 W1 W2 N0t N1t Q0t')
    eq(((-3*W0+4*W1-W2)/(2*h)+2*Q0t+N1t-2*N0t).subs({W1:W0+h*(N0t-Q0t),W2:W0+2*h*N1t}))
    # Countermodel: frozen pure outgoing transport, left one-sided
    # closure and centered interior. Exact discrete exponential state.
    x=S.symbols('x',positive=True);lplus=x+S.sqrt(1+x*x);lminus=x-S.sqrt(1+x*x)
    beta=(S.sqrt(1+x*x)-1)/(S.sqrt(1+x*x)+1)
    u=[lplus**j+beta*lminus**j for j in range(4)]
    eq(u[1]-(1+x)*u[0]);eq(u[2]-u[0]-2*x*u[1]);eq(u[3]-u[1]-2*x*u[2]);eq(u[2]-2*u[1]+u[0],2*x*x*u[0])
    eq(S.limit(beta/x**2,x,0),S.Rational(1,4))
    eq(S.limit((u[2]-2*u[1]+u[0])/x**2,x,0),2)
    # Continuum exp(sigma*y/a) has normalized second derivative 1.
    eq(S.diff(S.exp(x),x,2).subs(x,0),1)
    # Moving boundary energy current in physical flat principal geometry.
    p,q,r1,r2,r3,v=S.symbols('p q r1 r2 r3 v',real=True)
    grad=S.Matrix([q,r1,r2,r3]);ez=S.Matrix([1,0,0,0]);g2=grad.dot(grad)
    e=(p*p+g2)/2+v*p*q
    j=-p*grad-v*(q*grad+ez*(p*p-g2)/2)
    eq(S.expand(j[0]-v*e),-(p+v*q)*(q+v*p))
    eq(S.expand((j[0]-v*e).subs(q,-p)),(1-v)**2*p*p)
    eq(S.expand(e*e-j.dot(j)),(1-v*v)*(p*p-g2)**2/4)
    eq(e-(1-v)*(p*p+g2)/2,v*((p+q)**2+r1*r1+r2*r2+r3*r3)/2)
    # Source emission time maximizer: tau >= |dz| and |v_e|<1
    tau,dz,ve=S.symbols('tau dz ve',real=True)
    eq(-2*tau+2*dz*ve,-2*(tau-dz*ve))
    # Exact existing log/sqrt enclosure reused verbatim mathematically.
    def sq(x,scale=10**12):
        k=isqrt(x.numerator*scale**2//x.denominator)
        return Q(k,scale),Q(k+1,scale)
    def log(x,n=128):
        z=(x-1)/(x+1);a=2*sum(z**(2*j+1)/Q(2*j+1) for j in range(n))
        return a,a+2*z**(2*n+1)/(Q(2*n+1)*(1-z*z))
    a,b=sq(Q(145));c,d=sq(Q(2));lo=log((12+a)/(1+d))[0]-b/12+c;hi=log((12+b)/(1+c))[1]-a/12+d
    margins={'top_no_return_min_Y_2.01':2*Q('2.01')-Q(11,12)-hi,'radial_no_hit_R_3.01':Q('3.01')-Q('.04')-hi,'large_top_no_hit_Y_4.032':Q('4.032')-Q(11,12)-hi,'far_source_margin':Q('.1')-Q('.04')}
    for val in margins.values():assert val>0;n+=1
    # Extend the previous conservative fully discrete proof to t<=13,
    # so the original t=12 three-slot lookahead is covered.
    assert 1+13*Q('.03')<Q('1.2')**2;n+=1
    assert Q(3,2)*13*Q('1.2')<24;n+=1
    assert 39**2*2<56**2;n+=1
    assert 2*48+56==152;n+=1
    assert 2*152<400;n+=1
    assert Q(3,2)*13**2*3+48<900;n+=1
    assert max(Q(10,7),Q(900,400))<=Q(5,2);n+=1
    assert 4*152+5+Q(7,2)<617;n+=1
    a13,b13=sq(Q(170));hi13=log((13+b13)/(1+c))[1]-a13/13+d
    margins13={'top_no_return_min_Y_2.01':2*Q('2.01')-Q(12,13)-hi13,'radial_no_hit_R_3.01':Q('3.01')-Q('.04')-hi13,'large_top_no_hit_Y_4.032':Q('4.032')-Q(12,13)-hi13}
    for val in margins13.values():assert val>0;n+=1
    return dict(exact_checks=n,clock_span=[float(lo),float(hi)],causal_margin_lower={k:float(v) for k,v in margins.items()},extended_clock_upper=float(hi13),extended_causal_margin_lower={k:float(v) for k,v in margins13.items()},extended_CFL='dt*(7/dr+10/dy+400)<=1',extended_growth=617,scope='Exact source chart, time-graph, on-shell jet, temporal SBP and causal-current identities; conditional analytical trace theorem; not native kernel, actual independent stencil, or full production')

if __name__=='__main__':print(json.dumps(check(),indent=2))
