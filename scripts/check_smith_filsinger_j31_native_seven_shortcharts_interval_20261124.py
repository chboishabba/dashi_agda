#!/usr/bin/env python3
"""J31 exact rational seven-mode source local tubes and tangent envelopes.

Original finite-loss J23/J25 nine-state prescribed-wave smooth branches.
The first five J24 state boxes and J29 root brackets are external exact
source receipts: their membership in our input boxes is explicitly checked.
Sixth event state is ONLY an independent rational fixture (3/9 J24 box).
Does not prove full segments, 69D Krawczyk or orbit.
All interval arithmetic rounds outward to a rational 1e-30 grid.
"""
from fractions import Fraction as F
from math import factorial, isqrt
import json, argparse
from pathlib import Path
S=10**30

def down(q):
 q=F(q);return F(q.numerator*S//q.denominator,S)
def up(q):return -down(-F(q))
class I:
 __slots__=('a','b')
 def __init__(self,a,b=None,raw=False):
  if isinstance(a,I) and b is None:self.a,self.b=a.a,a.b;return
  a=F(a);b=a if b is None else F(b)
  assert a<=b
  self.a,self.b=(a,b) if raw else (down(a),up(b))
 def __add__(self,other):
  other=I(other);return I(self.a+other.a,self.b+other.b)
 __radd__=__add__
 def __neg__(self):return I(-self.b,-self.a)
 def __sub__(self,other):return self+-I(other)
 def __rsub__(self,other):return I(other)+-self
 def __mul__(self,other):
  other=I(other);v=[a*b for a in (self.a,self.b) for b in (other.a,other.b)]
  return I(min(v),max(v))
 __rmul__=__mul__
 def __truediv__(self,other):
  other=I(other);assert other.a*other.b>0,'singular denominator'
  return self*I(F(1,other.b),F(1,other.a))
 def __rtruediv__(self,other):return I(other)/self
 def square(self):return I(0 if self.a<=0<=self.b else min(self.a*self.a,self.b*self.b),max(self.a*self.a,self.b*self.b))
 def mag(self):return max(abs(self.a),abs(self.b))
 def within(self,o,strict=True):
  o=I(o);return o.a<self.a and self.b<o.b if strict else o.a<=self.a and self.b<=o.b
 def record(self):return [str(self.a),str(self.b)]
 def __repr__(self):return f'I({self.a},{self.b})'

class D:
 def __init__(self,x,d=None):self.x=I(x);self.d=[I(0) for _ in range(9)] if d is None else d
 def __add__(self,o):
  o=o if isinstance(o,D) else D(o);return D(self.x+o.x,[a+b for a,b in zip(self.d,o.d)])
 __radd__=__add__
 def __neg__(self):return D(-self.x,[-x for x in self.d])
 def __sub__(self,o):return self+-toD(o)
 def __rsub__(self,o):return toD(o)+-self
 def __mul__(self,o):
  o=toD(o);return D(self.x*o.x,[a*o.x+self.x*b for a,b in zip(self.d,o.d)])
 __rmul__=__mul__
 def __truediv__(self,o):
  o=toD(o);y=self.x/o.x;den=o.x.square()
  return D(y,[(a*o.x-self.x*b)/den for a,b in zip(self.d,o.d)])
 def __rtruediv__(self,o):return toD(o)/self

def toD(x):return x if isinstance(x,D) else D(x)
PARAM=dict(R1=F('0.35'),R2=F('0.28'),M=F('0.6'),L1=F('2'),L2=F('1.5'),
  k=F('0.35'),kh=F('2'),Rd=F('0.12'),Vd=F('0.1'),Gbleed=F('0.018'),
  Cb=F('0.65'),gamma=F('0.0152'),omega=F('1.1'),Rcoil=F('0.05'),
  Rgap=F('0.09'),Lh=F('0.15'),Ch=F('0.12'),Gload=F('0.52'))
MODES=((0,0,1),(0,1,1),(0,1,0),(0,1,1),(1,1,1),(1,0,1),(0,0,1))
STATES=[
 ['-0.04585851023046709','0.0967120405698972','1.9865816276887802','1.1890650910077614','2.3839347955003958','5.502919318568432','-5.781120275385947','-0.7451738522543331','-1.5585226674954609'],
 ['0.12348312106665','-0.33068865436942','-0.61498992005122','0.12478194459184','0.02478194459184','-1.26821663487563','8.05084491010875','0.29147231465058','1.36414548330839'],
 ['0.13523459842601','-0.37755904088316','-0.57949133558498','0.11808477566022','0.0018','-0.35976396951008','8.14678092946336','0.19549754734332','1.25957158565016'],
 ['0.13777688770661','-0.38794832888392','-0.56840423619862','0.11753667895618','0.006','-0.14428501896863','8.15470656353592','0.17836730293335','1.23181233103631'],
 ['0.1575089933189','-0.52392044646492','0.40607309976167','0.42213199004971','0.30607309976167','5.94776080307441','5.642624741628','-0.40580972792692','-0.2565046667794'],
 ['0.15431688550553','-0.51767847907243','0.4858280655798','0.45489512322921','0.35489512322921','6.23432987041079','5.32411883721043','-0.46942327080398','-0.35480689258185'],
 ['0.08472814436407','-0.32935984299057','1.33978173940005','0.83433116172484','1.23978173940005','8.13119780949747','0.42908731743842','-0.98106986849663','-1.1666415376269']]
TIMES=['0','3.389367008894','3.491292721190','3.515340479143','4.275489023275','4.323837945006','4.928751407316']
SIGNS=(1,-1,1,1,-1,-1)
# Source-owned J26–J29 first five and J30 sixth certified root brackets.
# This code checks geometric containment, not the upstream ODE proofs.
BRACKETS=(('3.389367008','3.389367010'),
 ('3.49129269','3.49129275'),('3.51534025','3.51534095'),
 ('4.275487825','4.27549016875'),
 ('4.32383391875','4.32384016875'),
 ('118763222704486979432589457030223322057/24096899911609601083074179150560000000',
  '118772079990387566784735834168684442057/24096899911609601083074179150560000000'))

def taylor_point(z,trig,n=36):
 """Rigorous rational sin/cos at rational point, explicit tail bound."""
 z=F(z);assert 0<=z<=7
 power=2*n+3 if trig=='sin' else 2*n+2
 terms=sum(((-1)**k*z**(2*k+(1 if trig=='sin' else 0))/factorial(2*k+(1 if trig=='sin' else 0)) for k in range(n+1)),F(0))
 tail=z**power/F(factorial(power))
 ratio=z*z/F((power+1)*(power+2));assert ratio<1
 err=tail/(1-ratio)
 return I(terms-err,terms+err)

def phase(t):
 t=I(t);m=(t.a+t.b)/2;radius=(t.b-t.a)/2
 z=F('0.3')+F('1.1')*m
 spread=F('1.1')*radius
 # |sin a-sin b|, |cos a-cos b| <= |a-b|
 cs=taylor_point(z,'cos')+I(-spread,spread)
 sn=taylor_point(z,'sin')+I(-spread,spread)
 return sn,cs

K=I(F(isqrt(3*S*S),S),F(isqrt(3*S*S)+1,S))*F(3,25)

def f(x,t,mode):
 U,V,chi=mode;P=PARAM
 i,j,u,v,b,q,r,ih,cap=x
 sn,co=phase(t)
 ju=(u-b-P['Vd'])/P['Rd'] if U else 0
 jv=(v-b-P['Vd'])/P['Rd'] if V else 0
 a=-P['R1']*i;bb=u-v-P['R2']*j
 left=-j-ju+P['k']*q+P['kh']*ih
 right=j-jv
 return [
   (P['L2']*a-P['M']*bb)/F('2.64'),(-P['M']*a+P['L1']*bb)/F('2.64'),
   (F('1.55')*left+right)/F('1.17'),(left+F('1.4')*right)/F('1.17'),
   (ju+jv-P['Gbleed']*b-chi*ih)/P['Cb'],
   P['omega']*r-P['gamma']*q-P['k']*u/F(2)+K*co,
   -P['omega']*q-P['gamma']*r-K*sn,
   (chi*b-cap-(P['Rcoil']+chi*P['Rgap'])*ih-P['kh']*u)/P['Lh'],
   (ih-P['Gload']*cap)/(P['Ch']*(1+F('1.5')*cap*cap))]

def fJ(X,t,mode):
 dual=[]
 for i,x in enumerate(X):
  d=[I(0)]*9;d[i]=I(1);dual.append(D(x,d))
 ans=f(dual,t,mode)
 return [z.x for z in ans],[z.d for z in ans]

def guard(k,x):
 return ((x[3]-x[4]-F('0.1')) if k in (0,4) else
         (x[2]-x[4]-F('0.1')) if k in (3,5) else
         x[4]-(F('0.0018') if k==1 else F('0.006')))
def guard_slope(k,fx):
 return ((fx[3]-fx[4]) if k in (0,4) else
         (fx[2]-fx[4]) if k in (3,5) else fx[4])

def certify_chart(k,h):
 mode=MODES[k];tc=F(TIMES[k]);xc=list(map(F,STATES[k]));h=F(h)
 start_radius=F(1,10000);time_radius=(F(0) if k==0 else F(1,5000) if k==6 else F(1,200000));tube_radius=F(1,1000)
 if 1<=k<=6:
  left,right=map(F,BRACKETS[k-1])
  assert tc-time_radius<left<right<tc+time_radius
 start=[I(a-start_radius,a+start_radius) for a in xc]
 tube=[I(a-tube_radius,a+tube_radius) for a in xc]
 t0=I(tc-time_radius,tc+time_radius)
 window=I(tc-time_radius,tc+time_radius+h)
 fx,J=fJ(tube,window,mode)
 pic=[a+I(0,h)*v for a,v in zip(start,fx)]
 if not all(x.within(y) for x,y in zip(pic,tube)):return None
 L=max(sum(v.mag() for v in row) for row in J)
 q=L*h
 if q>=1:return None
 # dx/dx0 Peano-Baker: I + h*J(tube) + nonnegative tail <= q^2/(1-q)
 tail=q*q/(1-q)
 Phi=[[I(int(i==j))+h*J[i][j]+I(-tail,tail) for j in range(9)] for i in range(9)]
 f0=f(start,t0,mode)
 # Endpoints vary in absolute source clock. The flow map obeys
 # dPhi/dt1=f(t1,Phi), dPhi/dt0=-D_xPhi*f(t0,x0).
 # These bounds hold on the correlated fixed-duration t1=t0+h slice,
 # NOT the full independent 69D event-time rectangle.
 f_terminal=f(tube,I(tc-time_radius+h,tc+time_radius+h),mode)
 dt_start=[-sum((Phi[i][j]*f0[j] for j in range(9)),I(0)) for i in range(9)]
 sn,co=phase(window)
 ft=[I(0) for _ in range(9)]
 ft[5]=-PARAM['omega']*K*sn;ft[6]=-PARAM['omega']*K*co
 acceleration=[ft[i]+sum((J[i][j]*fx[j] for j in range(9)),I(0)) for i in range(9)]
 end=[start[i]+h*f0[i]+(h*h/F(2))*acceleration[i] for i in range(9)]
 if not all(x.within(y,strict=False) for x,y in zip(end,tube)):
  raise AssertionError('Taylor2 endpoint excluded from previously valid Picard tube')
 # On a genuine zero-guard initial event, fixed post-event slope makes
 # its diode branch physically admissible for t>0. All *other* diode and
 # spark hysteresis guards must be strict over the whole Picard tube.
 gu=guard(3,tube);gv=guard(0,tube)
 U,V,chi=mode
 last=k-1 if k else -1
 if last not in (3,5):assert (gu.a>0 if U else gu.b<0)
 if last not in (0,4):assert (gv.a>0 if V else gv.b<0)
 if chi:assert (tube[4]-F('0.0018')).a>0
 else:assert (tube[4]-F('0.006')).b<0
 slope=[]
 if k:
  prev=guard_slope(k-1,f(tube,window,MODES[k-1]))
  post=guard_slope(k-1,fx)
  expected=SIGNS[k-1]
  if not (prev.a>0 if expected==1 else prev.b<0):return None
  if not (post.a>0 or post.b<0):return None
  slope=[prev.record(),post.record()]
 return dict(k=k,mode=list(mode),start_t=TIMES[k],h=str(h),
     original_source_smooth_rhs='J25/J31 nine-state fixed diode/spark branch',
     original_J24_rational_numerical_centre_seed_only=True,
     J29_original_full_J24_box_covered_by_chart=(1<=k<=5),
     J29_original_receipt_still_required=True,
     original_J29_source_proof_reexecuted_here=False,
     initial_ball_radius=str(start_radius),initial_time_radius=str(time_radius),
     proven_fulltime_picard_tube_radius=str(tube_radius),
     source_interval_f_guard_slope_pre_post=slope,
     endpoint_9D_Taylor2_interval=[v.record() for v in end],
     jacobian_9x9_endpoint_interval=[list(map(I.record,row)) for row in Phi],
     fixed_duration_slice_partial_start_time=[v.record() for v in dt_start],
     fixed_duration_slice_partial_end_time=[v.record() for v in f_terminal],
     independent_start_end_time_rectangle_Jacobian_proved=False,
     derivative_fulltube_inf_lipschitz_bound=str(L),peano_q=str(q),
     peano_tail_component_radius=str(tail),
     exact_Picard_inward=True,
     non_switching_physical_diodes_and_spark_thresholds_strict=True,
     after_switching_physical_mode_valid_if_event_guard_zero=True,
     fulltime_branch_slope_transverse=bool(k),
     original_source_full_chart_orbit_attached=False)

def main():
 ap=argparse.ArgumentParser();ap.add_argument('--out',type=Path,required=True);args=ap.parse_args()
 checks=[]
 for k in range(7):
  got=None
  for e in range(8,27):
   got=certify_chart(k,F(1,2**e))
   if got is not None:break
  if got is None:raise AssertionError(('No source Picard/slope certificate',k))
  checks.append(got)
 out=dict(status='PASS_SOURCE_RATIONAL_LOCAL_ALL_SEVEN_MODE_TUBES_NOT_GLOBAL_SHOOTING',
    rational_source_constants=True,original_physically_smooth_modes=7,
    exact_Picard_tubes=7,certified_9x9_variational_shortcharts=7,
    signed_pre_and_post_event_slopes=6,
    non_switching_guard_tubes=7,
    all_seven_modes_physically_admissible_conditional_on_event_zero=True,
    input_state_radius='1/10000',input_time_radii=['0']+['1/200000']*5+['1/5000'],
    J29_first_five_original_event_boxes_geometrically_covered=True,
    J29_J30_all_six_exact_root_time_brackets_geometrically_covered=True,
    actual_source_smooth_chart_seed_proof_for_first_five_requires_J29_receipt=True,
    sixth_full_J24_box_attached=False,
    original_full_seven_chart_69D_interval_certificate=False,
    strict_original_69D_Krawczyk=False,
    periodic_fixed_point_proved=False,source_pi_period_endpoint_in_this_cut=False,
    independent_smooth_chart_certificates=checks)
 args.out.parent.mkdir(parents=True,exist_ok=True)
 args.out.write_text(json.dumps(out,indent=2)+'\n')
 print(json.dumps({k:out[k] for k in ('status','exact_Picard_tubes','certified_9x9_variational_shortcharts','signed_pre_and_post_event_slopes')},indent=2))
 for x in checks:print('chart',x['k'],'h',x['h'],'q',float(F(x['peano_q'])),'slope',[(float(F(v[0])),float(F(v[1]))) for v in x['source_interval_f_guard_slope_pre_post']])
if __name__=='__main__':main()
