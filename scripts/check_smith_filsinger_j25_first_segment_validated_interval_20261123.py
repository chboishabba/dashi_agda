#!/usr/bin/env python3
"""Outward-rounded rational fixed-point tube for native J18 source-only early-time IVP.

Standalone exact rational/integer arithmetic. Proves only one small, diode-inactive,
spark-ON interval; does NOT certify the full period or the return-map fixed point.
All nonlinear terms, original nine states and both source quadratures retained.
"""
import json, math
from pathlib import Path
from fractions import Fraction as F

S = 10**30

def floor_div(n,d):return n//d
def ceil_div(n,d):return -((-n)//d)
class I:
    __slots__=('a','b')
    def __init__(self,a,b=None,raw=False):
        if raw: self.a=int(a);self.b=int(b)
        else:
            u=F(a);v=u if b is None else F(b)
            self.a=floor_div(u.numerator*S,u.denominator)
            self.b=ceil_div(v.numerator*S,v.denominator)
        assert self.a<=self.b
    def __add__(self,o):
        o=iv(o);return I(self.a+o.a,self.b+o.b,raw=True)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a,raw=True)
    def __sub__(self,o):return self+-iv(o)
    def __rsub__(self,o):return iv(o)+-self
    def __mul__(self,o):
        o=iv(o);v=[self.a*o.a,self.a*o.b,self.b*o.a,self.b*o.b]
        return I(floor_div(min(v),S),ceil_div(max(v),S),raw=True)
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o);assert o.a>0 or o.b<0
        # reciprocal via integer floor and ceil
        rec=I(floor_div(S*S,o.b),ceil_div(S*S,o.a),raw=True)
        return self*rec
    def __pow__(self,n):
        if n==0:return I(1)
        if n==2:
            if self.a>=0:return I(floor_div(self.a*self.a,S),ceil_div(self.b*self.b,S),raw=True)
            if self.b<=0:return I(floor_div(self.b*self.b,S),ceil_div(self.a*self.a,S),raw=True)
            return I(0,ceil_div(max(self.a*self.a,self.b*self.b),S),raw=True)
        raise ValueError(n)
    def clippos(self):return I(max(self.a,0),max(self.b,0),raw=True)
    def expand(self,eps):return I(self.a-iv(eps).b,self.b+iv(eps).b,raw=True)
    def subset(self,o):return self.a>=o.a and self.b<=o.b
    def intersects(self,o):o=iv(o);return not(self.b<o.a or o.b<self.a)
    def maxabs(self):return max(abs(self.a),abs(self.b))/S
    def width(self):return (self.b-self.a)/S
    def asfloat(self):return [self.a/S,self.b/S]
def iv(x):return x if isinstance(x,I) else I(x)

def sin_rational_0_to_1(x):
    x=F(x);assert 0<=x<=F(1)
    approx=sum(((-1)**k*x**(2*k+1))/math.factorial(2*k+1) for k in range(8))
    rem=x**17/F(math.factorial(17))
    return I(approx-rem,approx+rem)
def cos_rational_0_to_1(x):
    x=F(x);assert 0<=x<=F(1)
    approx=sum(((-1)**k*x**(2*k))/math.factorial(2*k) for k in range(8))
    rem=x**16/F(math.factorial(16))
    return I(approx-rem,approx+rem)

def trig_bounds(t0,t1):
    a=F('0.3')+F('1.1')*F(t0)
    b=F('0.3')+F('1.1')*F(t1)
    assert 0<a<=b<1
    l=sin_rational_0_to_1(a);u=sin_rational_0_to_1(b)
    sinx=I(l.a,u.b,raw=True)
    assert sinx.a>0 # cosine derivative is negative on this angle sector
    l=cos_rational_0_to_1(b);u=cos_rational_0_to_1(a)
    cosx=I(l.a,u.b,raw=True)
    assert cosx.a>0 # sine derivative is positive on this sector
    return sinx,cosx

def sqrt_03():
    # exact integer root bounds sqrt(3/100) at 1e-30 grid
    v=math.isqrt(3*S*S//100)
    return I(v,v+1,raw=True)
RAD=sqrt_03()

PARAM={k:I(v) for k,v in dict(
 L1='2',L2='1.5',M='.6',R1='.35',R2='.28',C='1',Cu='.4',Cv='.55',Cb='.65',
 Rd='.12',Vd='.1',Gbleed='.018',Von='.006',Voff='.0018',omega='1.1',
 gamma_rad='.015',gamma_internal='.0002',k='.35',source_amp='1.2',
 Lh='.15',Ch='.12',alpha='.5',Rgap='.09',Rcoil='.05',Gload='.52',kh='2').items()}

def f(t0,t1,x,on=True):
    i,j,u,v,b,q,r,ih,c=x;p=PARAM
    sin,cos=trig_bounds(t0,t1)
    sr=p['source_amp']*cos
    si=-p['source_amp']*sin
    ju=((u-b-p['Vd'])/p['Rd']).clippos()
    jv=((v-b-p['Vd'])/p['Rd']).clippos()
    # inverse inductance det=2*1.5-0.6^2 = 2.64
    a=-p['R1']*i
    bb=u-v-p['R2']*j
    di=(p['L2']*a-p['M']*bb)/I('2.64')
    dj=(-p['M']*a+p['L1']*bb)/I('2.64')
    # inverse A, det=1.4*1.55 - 1 = 1.17
    left=-j-ju+p['k']*q+p['kh']*ih
    right=j-jv
    du=(I('1.55')*left+right)/I('1.17')
    dv=(left+I('1.4')*right)/I('1.17')
    db=(ju+jv-p['Gbleed']*b-I(int(on))*ih)/p['Cb']
    gam=p['gamma_rad']+p['gamma_internal']
    dq=p['omega']*r-gam*q-p['k']*u/I(2)+RAD*sr
    dr=-p['omega']*q-gam*r+RAD*si
    dih=(I(int(on))*b-c-(p['Rcoil']+I(int(on))*p['Rgap'])*ih-p['kh']*u)/p['Lh']
    dc=(ih-p['Gload']*c)/(p['Ch']*(I(1)+I('1.5')*c**2))
    return [di,dj,du,dv,db,dq,dr,dih,dc]

def box_center(c,r):return [I(F(str(v))-r,F(str(v))+r) for v in c]
# Decimal rational seed from the original J23 two-switch numerical receipt.
# An exact rational centre, NOT a certified periodic fixed point.
ROOT=['-0.04585851023046709','0.0967120405698972','1.9865816276887802',
      '1.1890650910077614','2.3839347955003958','5.502919318568432',
      '-5.781120275385947','-0.7451738522543331','-1.5585226674954609']

def jacobian_infinity_lipschitz_bound(tube):
    """Exact outward interval derivative on the verified ON / no-diode tube."""
    p=PARAM; c=tube[8]; ih=tube[7]
    z=I(0); J=[[z for _ in range(9)] for _ in range(9)]
    J[0][0]=-p['R1']*I('1.5')/I('2.64')
    J[0][1]=p['M']*p['R2']/I('2.64')
    J[0][2]=-p['M']/I('2.64'); J[0][3]=p['M']/I('2.64')
    J[1][0]=p['M']*p['R1']/I('2.64')
    J[1][1]=-p['L1']*p['R2']/I('2.64')
    J[1][2]=p['L1']/I('2.64');J[1][3]=-p['L1']/I('2.64')
    J[2][1]=-I('.55')/I('1.17')
    J[2][5]=I('1.55')*p['k']/I('1.17')
    J[2][7]=I('1.55')*p['kh']/I('1.17')
    J[3][1]=I('.4')/I('1.17')
    J[3][5]=p['k']/I('1.17'); J[3][7]=p['kh']/I('1.17')
    J[4][4]=-p['Gbleed']/p['Cb'];J[4][7]=-I(1)/p['Cb']
    J[5][2]=-p['k']/I(2)
    J[5][5]=-p['gamma_rad']-p['gamma_internal'];J[5][6]=p['omega']
    J[6][5]=-p['omega'];J[6][6]=-p['gamma_rad']-p['gamma_internal']
    J[7][2]=-p['kh']/p['Lh'];J[7][4]=I(1)/p['Lh']
    J[7][7]=-(p['Rcoil']+p['Rgap'])/p['Lh'];J[7][8]=-I(1)/p['Lh']
    g=I(1)+I('1.5')*c**2
    J[8][7]=I(1)/(p['Ch']*g)
    J[8][8]=-p['Gload']/(p['Ch']*g)-(ih-p['Gload']*c)*I(3)*c/(p['Ch']*g**2)
    upper=max(sum(max(abs(x.a),abs(x.b)) for x in row) for row in J)
    # Divide [0,1/11] into four equal time parts; 1/44 * L < 1.
    assert upper*1 < S*44
    return dict(max_infty_jacobian_norm_upper=ceil_div(upper,1)/S,
                exact_Jacobian_row_norm_upper_integer=upper,
                time_part_for_picard_contraction='1/44',
                strict_contraction_on_each_part=upper < 44*S,
                conservatively_bounded_by_44=True)

def run(h=F(1,11)):
    assert h<=F(1,11)
    initial=box_center(ROOT,F(1,10**7))
    center=box_center(ROOT,F(0))
    d0=f(0,h,initial,True)
    # Candidate tube radii computed entirely with outward-rounded integers.
    radii=[max(S//10000,ceil_div(max(abs(e.a),abs(e.b))*h.numerator*11,10*h.denominator))
           for e in d0]
    # Eventual enclosure only depends on exact self-inclusion verification;
    # the radius-generation heuristic is NOT used as a theorem premise.
    included=False
    for n in range(100):
        tube=[I(c.a-v,c.b+v,raw=True) for c,v in zip(center,radii)]
        derivative=f(0,h,tube,True)
        cover=[a+I(0,h)*d for a,d in zip(initial,derivative)]
        if all(c.subset(t) for c,t in zip(cover,tube)):
            included=True
            break
        required=[max(abs(c.a-z.a),abs(c.b-z.b))+S//(10**7)
                  for c,z in zip(cover,center)]
        radii=[max(r,ceil_div(26*q,25)) for r,q in zip(radii,required)]
        assert max(radii)<10*S,'Picard tube too wide'
    assert included,'Picard enclosure failed'
    picard_slack=[min(c.a-t.a,t.b-c.b) for c,t in zip(cover,tube)]
    assert min(picard_slack)>=0
    gu=tube[2]-tube[4]-PARAM['Vd']
    gv=tube[3]-tube[4]-PARAM['Vd']
    gs=tube[4]-PARAM['Voff']
    assert gu.b<0 and gv.b<0 and gs.a>0
    assert (I(1)+I('1.5')*tube[8]**2).a>=S
    local_lipschitz=jacobian_infinity_lipschitz_bound(tube)
    return dict(status='PASS_VALIDATED_LOCAL_FLOW_TUBE_PICARD',duration=str(h),
      initial_state_halfwidth='1e-7',iterations_to_exact_inclusion=n+1,
      radii=[I(v,v,raw=True).asfloat()[0] for v in radii],
      radii_integer_grid=radii,
      exact_Picard_self_inclusion_slack_integer_grid=picard_slack,
      diode_U_guard_interval=gu.asfloat(),diode_V_guard_interval=gv.asfloat(),
      spark_off_guard_interval=gs.asfloat(),
      exact_guards_integer_grid=dict(U=[gu.a,gu.b],V=[gv.a,gv.b],spark_OFF=[gs.a,gs.b]),
      exact_picard_inclusion=True,initial_spark_mode='ON',
      verified_guard_free_segment=True,local_lipschitz=local_lipschitz,
      exact_integer_outward_rounding_scale=str(S),
      positive_sqrt_radiative_exact_grid=True,
      trigonometric_taylor_remainder_rational=True,
      source_model='J18 nine-state source-only equations independently transcribed, rational model coefficients',
      covers_first_diode_event=False,full_tau_shooting_interval_proved=False,
      certified_current_exact_periodic_root=False,no_physical_source_metrology=True)

def run_wide_five_parameter_box():
    global RAD
    bounds=dict(gamma_rad=('0.0149','0.0151'),
                gamma_internal=('0.00015','0.00025'),
                k=('0.3495','0.3505'),kh=('1.9995','2.0005'),
                Gload=('0.5195','0.5205'))
    for key,(a,b) in bounds.items():PARAM[key]=I(F(a),F(b))
    # 2 gamma_rad in [0.0298,0.0302]; integer square-root enclosure.
    low=F('0.0298')*S*S
    high=F('0.0302')*S*S
    ll=math.isqrt(low.numerator//low.denominator)
    uu=math.isqrt(high.numerator//high.denominator)+1
    RAD=I(ll,uu,raw=True)
    r=run()
    r['uniform_fixed_initial_state_box_over_parameters']=bounds
    r['not_uniform_periodic_fixed_point_box']=True
    return r

if __name__=='__main__':
 nominal=run()
 wide=run_wide_five_parameter_box()
 print(json.dumps(dict(status='PASS_TWO_VALIDATED_FIRST_SEGMENT_TUBES',
       nominal=nominal,wide_five_parameter_box=wide,
       whole_tau_interval_proof_complete=False),indent=2))
