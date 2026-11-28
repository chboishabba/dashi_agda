"""Original F8 cap diamond, boundary collars and transverse Green series.
Conditional on original smooth-reference finite propagation. No signed receiver solve.
"""
from fractions import Fraction as Q
from math import factorial, comb
import json
import sympy as S
from check_f8_global_wall_kernel import Fbox
from check_f8_fixed_window_causal_cap import root, sub, shift, bracket, run as cap

def geometry():
    cap()
    f=Fbox(Q(1)); span=sub(Fbox(Q(1,12)),f);end=shift(span,-Q(1,20))
    smax=Q(9,20000);dmax=Q(7,20000)
    tmin=end[0]-dmax;Lmin=tmin-smax;Tmax=end[1]
    blo=Q('.087590020348');bslo=Q('.999681');brhi=Q('.087622')
    assert Lmin>Q('2.65') and Tmax<Q('2.66') and bslo-brhi>Q('.91')
    rlo=root(span[0]**2-Q(11,12)**2)[0]-Q(3,250)
    reachhi=root(end[1]**2-(1-blo-Q('0.000000000004'))**2)[1]
    assert reachhi<Q('2.5') and rlo-Q(1,25)>0
    rho=Q(361,10**6);assert reachhi-rlo+Q(1,25)<rho
    slack=5*rho
    # In the odd radial lift no image at r<=0 can reach this receiver.
    assert rlo>reachhi
    rstart=Q(396,10000);rdiff=rlo-Q(1,25);assert rdiff>Q('2.49')
    rpath=rstart-slack/(4*rdiff);assert rpath>Q('.0394')
    # Any causal intermediate point satisfies |X-X_linear|² <= lambda(1-lambda) slack.
    # Complete square in sqrt(1-lambda) for z lower bound.
    zlo=blo-slack/(4*(bslo-brhi));assert zlo>Q('.087')>Q(1,13)
    # For intermediate causal subsegments Minkowski reverse triangle gives q_sub<=q_total.
    eta=slack/(4*Q('.087')**2);assert eta<Q(1,16)
    # Convex wall is below secants through certified upper b at three elapsed nodes.
    ts=list(map(Q,('.01','1.3','2.644')))
    brackets=[('.992941461624','.992941461626'),('.332447023116','.332447023119'),('.088922710539','.088922710543')]
    bh=[bracket(shift(f,t),*p)[1] for t,p in zip(ts,brackets)]
    # Lower linear endpoint chord: lambda<=t/tmin. Bound lambda(1-lambda)
    # by t/tmin for first interval, (Tmax-t)/Lmin for second.
    sag=[bslo-(bslo-blo)*t/tmin-b for t,b in zip(ts,bh)]
    margins=[]
    for j in range(2):
        a,b=ts[j:j+2];x,y=sag[j:j+2];assert min(x,y)>0
        m=(y-x)/(b-a)
        # Quadratic min on interval checked exactly including possible interior vertex.
        va=slack*(a/tmin if j==0 else (Tmax-a)/Lmin)
        slope=slack*(1/tmin if j==0 else -1/Lmin)
        c=x*x-va;lin=2*x*m-slope;quad=m*m;h=b-a
        vals=[c,c+lin*h+quad*h*h]
        if quad and 0<-lin/(2*quad)<h:vals.append(c-lin*lin/(4*quad))
        assert min(vals)>0;margins.append(float(min(vals)))
    # Exact original forward/reverse time collar bounds. No interior wall contact in [0.01,2.644].
    assert Tmax-ts[-1]<Q('.0152')
    return dict(slack_upper=str(slack),z_lower=float(zlo),radial_path_lower=float(rpath),negative_image_excluded=True,eta_upper=float(eta),excluded_wall_elapsed=[float(ts[0]),float(ts[-1])],emission_collar_upper=.01,receiver_collar_upper=.0152,strict_squared_gap_lower=margins,scope='all causal paths between original admissible source/receiver points; includes broken paths, not only null chords')

def coeff(n):
    a=Q(1)
    for j in range(n):a*=Q((2*j-3)*(2*j+5),4*(j+1)**2)
    return a*Q(4**n,comb(2*n,n))

def series():
    n=S.symbols('n',integer=True,positive=True);z,xi=S.symbols('z xi',positive=True);t,x,y,w=S.symbols('t x y w',real=True)
    q=t*t-x*x-y*y-w*w-(z-xi)**2;alpha=S.symbols('alpha');f=S.Function('f')(z);g=S.Function('g')(q)
    P=lambda a:S.diff(a,t,2)-sum(S.diff(a,v,2) for v in (x,y,w,z))+S.Rational(15,4)/z**2*a
    # Chain rule in 1+4 dimensions. Retain derivatives of the distribution in q.
    # Check on symbolic power with formal q derivatives via simplified ratios.
    assert S.expand(S.diff(q,t,2)-sum(S.diff(q,v,2) for v in (x,y,w,z)))==10
    assert S.expand(S.diff(q,t)**2-sum(S.diff(q,v)**2 for v in (x,y,w,z))-4*q)==0
    assert S.expand(-2*S.diff(q,z)-4*(z-xi))==0
    # Coefficient recurrence for q_+^(n-3/2) (analytic-continuation distribution).
    a=n-S.Rational(3,2);fn=z**(-n);prev=z**(1-n)
    assert S.simplify((4*a*n*fn+4*a*(z-xi)*S.diff(fn,z))/(4*a*n*xi*z**(-n-1)))==1
    assert S.simplify((-S.diff(prev,z,2)+S.Rational(15,4)/z**2*prev)/z**(-n-1)-(S.Rational(15,4)-n*(n-1)))==0
    # beta/Abel coefficients and recurrence, with signed source/target symmetric factors.
    for j in range(1,25):
        d=coeff(j);p=coeff(j-1)
        assert d==p*Q((2*j-5)*(2*j+3),2*j*(2*j-1))
        A=(Q(j)-Q(1,2))*d;B=(Q(j-1)-Q(1,2))*p
        assert A==B*Q((2*j-5)*(2*j+3),2*j*(2*j-3))
    # Ratio magnitude <1 for n>=2. Tail after order N of analytic factor
    # and its first four derivatives on 0<=eta<=1/16.
    assert coeff(0)==1 and coeff(1)==Q(-15,2) and coeff(2)==Q(35,8)
    assert S.expand((n+1)*(n+S.Rational(1,2))-(n-S.Rational(3,2))*(n+S.Rational(5,2)))==n/2+S.Rational(17,4)
    N=24;e=Q(1,16);tails=[]
    for j in range(5):
        first=abs(coeff(N+1))*Q(factorial(N+1),factorial(N+1-j))*e**(N+1-j)
        ratio=e*Q(N+2,N+2-j);assert ratio<1
        tails.append(first/(1-ratio))
    return dict(order=N,coefficients=[str(coeff(j)) for j in range(5)],analytic_factor_derivative_tail_upper=[float(x) for x in tails],exact_tail_fractions=[str(x) for x in tails],scope='analytic factor only; leading distribution and wall operator not bounded by these scalar tails')

if __name__=='__main__':print(json.dumps(dict(geometry=geometry(),series=series()),indent=2))
