#!/usr/bin/env python3
"""J28 independent exact-rational Picard proof for event 3 from J27 certified event box.
Source: original J25/J27 nine-state equations and J24's proven spark-OFF event box.
No hardware claim; this certifies the first OFF->ON crossing only, not a periodic orbit.
"""
from fractions import Fraction as F
import math,json
S=10**22

def floor(n,d): return n//d
def ceil(n,d): return -((-n)//d)
class I:
    __slots__=('a','b')
    def __init__(self,a,b=None,raw=False):
        if raw:self.a=int(a);self.b=int(b)
        else:
            x=F(a);y=x if b is None else F(b)
            self.a=floor(x.numerator*S,x.denominator)
            self.b=ceil(y.numerator*S,y.denominator)
        assert self.a<=self.b
    def __add__(self,x):
        x=iv(x);return I(self.a+x.a,self.b+x.b,True)
    __radd__=__add__
    def __neg__(self):return I(-self.b,-self.a,True)
    def __sub__(self,x):return self+-iv(x)
    def __rsub__(self,x):return iv(x)+-self
    def __mul__(self,x):
        x=iv(x);v=(self.a*x.a,self.a*x.b,self.b*x.a,self.b*x.b)
        return I(floor(min(v),S),ceil(max(v),S),True)
    __rmul__=__mul__
    def __truediv__(self,x):
        x=iv(x);assert x.a>0 or x.b<0
        return self*I(floor(S*S,x.b),ceil(S*S,x.a),True)
    def sq(self):
        x=iv(self)
        if x.a>=0:return I(floor(x.a*x.a,S),ceil(x.b*x.b,S),True)
        if x.b<=0:return I(floor(x.b*x.b,S),ceil(x.a*x.a,S),True)
        return I(0,ceil(max(x.a*x.a,x.b*x.b),S),True)
    def subset(self,x):return self.a>=x.a and self.b<=x.b
    def maxabs(self):return max(abs(self.a),abs(self.b))/S
    def fl(self):return [self.a/S,self.b/S]
    def expand(self,delta):
        z=iv(delta);return I(self.a-z.b,self.b+z.b,True)
    def hull(self,x):return I(min(self.a,x.a),max(self.b,x.b),True)
    def intersect(self,x):return I(max(self.a,x.a),min(self.b,x.b),True)
def iv(x):return x if isinstance(x,I) else I(x)
P={k:I(v) for k,v in dict(L1='2',L2='1.5',M='.6',R1='.35',R2='.28',C='1',Cu='.4',Cv='.55',Cb='.65',Rd='.12',Vd='.1',Gbleed='.018',Von='.006',Voff='.0018',omega='1.1',gamma_rad='.015',gamma_internal='.0002',k='.35',source_amp='1.2',Lh='.15',Ch='.12',alpha='.5',Rgap='.09',Rcoil='.05',Gload='.52',kh='2').items()}
# Exact 1e22 directed integer-grid radical bounds.
sqrt03=math.isqrt(3*S*S//100)
RAD=I(sqrt03,sqrt03+1,True)

def trig_point(theta,K=22):
    """Conservative exact Taylor + Lagrange at rational theta in [4,5]."""
    theta=F(theta);assert F(4)<theta<F(5)
    ss=sum(((-1)**k*theta**(2*k+1)/math.factorial(2*k+1) for k in range(K+1)),F(0))
    cc=sum(((-1)**k*theta**(2*k)/math.factorial(2*k) for k in range(K+1)),F(0))
    # Taylor's bound using the magnitude of the next missing term, enlarged
    # to a general Lagrange remainder of the preceding polynomial degree.
    rs=theta**(2*K+2)/math.factorial(2*K+2)
    rc=theta**(2*K+1)/math.factorial(2*K+1)
    return I(ss-rs,ss+rs),I(cc-rc,cc+rc)

def trig(t0,t1):
    # Both sin and cos are globally 1-Lipschitz.
    mid=F('.3')+F('1.1')*(F(t0)+F(t1))/2
    dr=F('1.1')*(F(t1)-F(t0))/2
    sn,co=trig_point(mid)
    return sn.expand(dr),co.expand(dr)

def field(t0,t1,X):
    i,j,u,v,b,q,r,ih,x=X;p=P
    sn,co=trig(t0,t1)
    sr=p['source_amp']*co;si=-p['source_amp']*sn
    jv=(v-b-p['Vd'])/p['Rd']
    a=-p['R1']*i;bb=u-v-p['R2']*j
    di=(p['L2']*a-p['M']*bb)/I('2.64')
    dj=(-p['M']*a+p['L1']*bb)/I('2.64')
    left=-j+p['k']*q+p['kh']*ih;right=j-jv
    du=(I('1.55')*left+right)/I('1.17')
    dv=(left+I('1.4')*right)/I('1.17')
    db=(jv-p['Gbleed']*b)/p['Cb'] # spark OFF; no ih sink
    gam=p['gamma_rad']+p['gamma_internal']
    dq=p['omega']*r-gam*q-p['k']*u/I(2)+RAD*sr
    dr=-p['omega']*q-gam*r+RAD*si
    dih=(-x-p['Rcoil']*ih-p['kh']*u)/p['Lh'] # spark OFF; no bank drive or Rgap
    dx=(ih-p['Gload']*x)/(p['Ch']*(I(1)+I('1.5')*x.sq()))
    return [di,dj,du,dv,db,dq,dr,dih,dx]

def picard_step(X,t0,t1):
    h=F(t1)-F(t0)
    B=[x.expand(F('0.00001')) for x in X]
    used=0
    for it in range(200):
        D=field(t0,t1,B)
        C=[x+I(0,h)*d for x,d in zip(X,D)]
        if all(c.subset(b) for c,b in zip(C,B)):
            used=it+1
            assert all((b.b-c.b)>=0 and (c.a-b.a)>=0 for b,c in zip(B,C))
            end=[x+I(h)*d for x,d in zip(X,D)]
            return end,B,D,used
        B=[b.hull(c).expand(F('0.000000001')) for b,c in zip(B,C)]
    raise RuntimeError('Picard inclusion failed at '+str((t0,t1))+' B='+str([x.fl() for x in B]))

def event_guards(B):
    return B[2]-B[4]-P['Vd'], B[3]-B[4]-P['Vd']

def run():
    # J27 proves that the entire state at the spark-OFF root lies in this
    # original J24 box. Its b-component is sharpened using the exact guard b=Voff.
    xs=['0.13523459842601','-0.37755904088316','-0.57949133558498','0.11808477566022','0.0018','-0.35976396951008','8.14678092946336','0.19549754734332','1.25957158565016']
    X=[I(F(v)-F('.0001'),F(v)+F('.0001')) for v in xs]
    X[4]=I('.0018')
    t0lo=F('3.49129269');t0hi=F('3.49129275')
    # Source-time interval is kept uncertain throughout: s is elapsed
    # exact rational time after an unknown t_OFF in the certified bracket.
    end=F('0.04');h=F('0.002');s=F(0)
    witnesses=[]
    bank_at_0022=None;bank_at_0026=None
    while s<end:
        s1=min(s+h,end)
        e,B,D,it=picard_step(X,t0lo+s,t0hi+s1)
        gu,gv=event_guards(B)
        assert gu.b<0 and gv.a>0,(str(s),gu.fl(),gv.fl())
        assert D[4].a>0,(str(s),D[4].fl())
        witnesses.append({'s0':str(s),'s1':str(s1),'picard_iterations':it,'U_guard':gu.fl(),'V_guard':gv.fl(),'bank_slope':D[4].fl(),'bank_end':e[4].fl(),
          'U_guard_grid':[str(gu.a),str(gu.b)],'V_guard_grid':[str(gv.a),str(gv.b)],
          'bank_slope_grid':[str(D[4].a),str(D[4].b)]})
        if s1==F('.022'):bank_at_0022=e[4]
        if s1==F('.026'):bank_at_0026=e[4]
        X=e;s=s1
    assert X[4].a>P['Von'].b,('spark-ON not forced by end',X[4].fl())
    # The root is strictly after s=0.022 and before s=0.026 by
    # exact outward-grid endpoint enclosures (not floating-point tests).
    assert bank_at_0022.b<P['Von'].a and bank_at_0026.a>P['Von'].b
    return {'status':'PASS_EXACT_RATIONAL_J28_THIRD_EVENT_EXISTENCE_UNIQUENESS',
      'prior_state':'entire J27 9/9 source-validated J24 spark-OFF box intersected with exact b=Voff',
      'source_time_uncertainty':[str(t0lo),str(t0hi)],'virtual_off_duration':str(end),
      'picard_accepted_pieces':len(witnesses),
      'bank_at_start_exact':'.0018','bank_at_end':X[4].fl(),
      'spark_ON_bracket_model_time':['3.51329269','3.51729275'],
      'bank_at_s_0022_grid':[str(bank_at_0022.a),str(bank_at_0022.b)],
      'bank_at_s_0026_grid':[str(bank_at_0026.a),str(bank_at_0026.b)],
      'minimum_guard_U_upper_grid':str(max(w['U_guard_grid'][1] for w in witnesses)),
      'minimum_guard_V_lower_grid':str(min(w['V_guard_grid'][0] for w in witnesses)),
      'minimum_bank_slope_grid':str(min(w['bank_slope_grid'][0] for w in witnesses)),
      'positive_bank_slope_all_pieces':True,'U_diode_inactive_all_pieces':True,'V_diode_active_all_pieces':True,
      'spark_ON_unique_before':str(t0hi+end),'spark_ON_event_state_J24_box_inclusion':False,
      'periodic_orbit_certified':False,'physical_original_source':False,'method':'exact integer-grid outward rounding + fixed-point Picard self-inclusion; trig Taylor+Lipschitz',
      'witnesses':witnesses}

if __name__=='__main__': print(json.dumps(run(),indent=2))
