"""Original F8 all-frequency self-collar majorant and tighter wall-contact guards.
No full cross-collar or receiver sign certificate. Exact rational checks.
"""
from fractions import Fraction as Q
from functools import lru_cache
from math import isqrt
import json
import sympy as S

# Same rational clock owner check_f8_global_wall_kernel.Fbox in checkout.
from check_f8_global_wall_kernel import Fbox

def root(x):
    d=10**20;n=isqrt((x*d*d).numerator//(x*d*d).denominator)
    return Q(n,d),Q(n+1,d)

def clock(t,f):
    lo,hi=Q(1,12),Q(1)
    for _ in range(48):
        m=(lo+hi)/2; a,b=Fbox(m)
        if a>f[1]+t:lo=m
        elif b<f[0]+t:hi=m
        else:raise AssertionError('clock comparison unresolved')
    return lo,hi

def direction(p):
    p=Q(p);assert -1<p<1
    return 2*p/(1+p*p),(1-p*p)/(1+p*p)

def geometry():
    f=Fbox(Q(1));g=Fbox(Q(1,12));T=(g[0]-f[1]-Q(1,20),g[1]-f[0]-Q(1,20))
    span=(T[0]+Q(1,20),T[1]+Q(1,20));R=root(span[0]**2-Q(11,12)**2)[0]-Q('.012')-Q('.04')
    be=(Q('.087590020348'),Q('.087590020352'));assert Fbox(be[0])[0]>g[1]-Q(1,20) and Fbox(be[1])[1]<g[0]-Q(1,20)
    # Rational support directions are proposals only. Every inequality is checked.
    times=list(map(Q,['.0037','.004','.005','.01','.025','.05','.1','.2','.4','.6','.8','1','1.3','1.6','1.9','2.2','2.4','2.5','2.6','2.63','2.64','2.645','2.648','2.649','2.6492']))
    boxes=[clock(t,f) for t in times]; margins=[]
    for i in range(len(times)-1):
        a,b=times[i:i+2];m=(a+b)/2;bm=sum(boxes[i]+boxes[i+1])/4
        # choose rational stereographic direction near midpoint average slopes
        u=(bm-1)/m;v=(sum(be)/2-bm)/(sum(T)/2-m)
        p=u/(1+root(1-u*u)[0]);q=v/(1+root(1-v*v)[0]);den=10**7
        p=Q(round(p*den),den);q=Q(round(q*den),den)
        u,cu=direction(p);v,cv=direction(q)
        c=v/cv-u/cu;assert c>0
        # D(t,0)+D(T*,t) <= t/cu+(T*-t)/cv+u/cu-v*b_e/cv+c*b(t).
        # Convex b and positive c make this upper function convex; check endpoints.
        vals=[t/cu+(T[1]-t)/cv+u/cu-v*be[1]/cv+c*box[1] for t,box in zip((a,b),boxes[i:i+2])]
        assert max(vals)<R,(float(a),float(b),float(R-max(vals)))
        margins.append(R-max(vals))
    assert T[1]-times[-1]<Q('.01')
    assert boxes[0][0]>Q('.997') and boxes[-1][1]<Q('.09')
    return dict(excluded=[float(times[0]),float(times[-1])],intervals=len(margins),reach_margin_lower=float(min(margins)),emission_h='.0037',reception_h='.01',emission_b_lower='.997',reception_b_lower='.087',scope='all wall contacts on contributing causal paths, monotonic endpoint reach and convex support upper')

def bounds():
    x,theta,k,tau,D,N=S.symbols('x theta k tau D N',positive=True)
    # J1=-J0': angular integral and derivative transfer use signed J1.
    assert S.simplify(S.diff(S.besselj(0,k*D),D)+k*S.besselj(1,k*D))==0
    assert S.simplify(S.diff(S.cos(theta)/S.sin(theta),theta)+1/S.sin(theta)**2)==0
    # For x>=1 split at eps=1/sqrt(x); 2eps+4cot(eps)/x <=6/sqrt(x).
    # pi>3 -> |J1|<=2/sqrt(x). For x<1 use integral |J1|<=1.
    assert Q(333,106)>3
    # Local eta and B regular guards from previous weak owner; now tighter h.
    rows=[];Csum=Q(0);Bsum=Q(0)
    for name,h,bl,a in [('E',Q('.0037'),Q('.997'),Q('.26')),('R',Q('.01'),Q('.087'),Q('.09'))]:
        B=Q(3,2)/bl;assert h*h/(4*bl*bl)<Q(1,16)
        assert Q(5,4)-Q(15,8)*(a*h*h/2)/bl>0
        # |N k J1(kD)/D| <= a sqrt(k) sqrt(tau) s_min^-3/4 <=2 a sqrt(k) sqrt(tau)
        assert 2**3<2**4 # (1/2)^(-3/4)<2
        # e^-lambda t weighted convolution: B/lambda+2a sqrt(k) Gamma(3/2)/lambda^(3/2)
        # lambda=4B+4(a²|k|)^(1/3) makes <=1/2. Gamma(3/2)<1.
        assert Q(22,7)<4
        c=Q('.41') if name=='E' else Q('.21');assert c**3>=a*a
        C=4*h*c;Csum+=C;Bsum+=4*h*B
        rows.append(dict(collar=name,h=str(h),B=str(B),a=str(a),growth_constant_upper=str(C),constant_exponent=str(4*h*B),inverse_bound='2 exp(4Bh + 4h(a²|k|)^(1/3))'))
    # BIDI two self inverses: 4 exp(Bsum+Csum k^(1/3)); trade Gevrey2 exponent delta.
    delta=Q(1,100);loss=4*Csum**3/(27*delta**2)
    y,c,d=S.symbols('y c d',positive=True);p=c*y*y-d*y**3;Y=2*c/(3*d)
    assert S.expand(4*c**3/(27*d*d)-p-(c+3*d*y)*(2*c-3*d*y)**2/(27*d*d))==0
    assert loss< Q('.01') and Bsum+loss<1
    # Conditional weight budget independent of cross-collar projection.
    return dict(rows=rows,combined_C=str(Csum),combined_C_display=float(Csum),combined_constant_exponent=str(Bsum),gevrey_weight_loss=str(delta),extra_exponent_upper=str(loss),extra_exponent_display=float(loss),combined_prefactor_upper=12,scope='each full radial self-collar Fourier mode, all k; two local inverses on compatible Gevrey2 weights, no cross transport bound or total sign')

if __name__=='__main__':print(json.dumps(dict(geometry=geometry(),bounds=bounds()),indent=2))
