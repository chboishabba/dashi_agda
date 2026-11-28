"""Outward rational prefix material and storage enclosure, fixed binary ingress.
Original pair reaction and held-power thermal law; no rounded field replay used.
All constants are the exact binary inputs/literals. Geometry uncertainty external.
"""
from fractions import Fraction as F
from dataclasses import dataclass
import numpy as np
from solar_event_rounding import q,sqrt_interval
from solar_population_event import MASS,CHARGE

BITS=128


def round_bound(v,upper):
    v=q(v)
    if not v:return v
    shift=BITS-(abs(v.numerator).bit_length()-v.denominator.bit_length())
    scale=F(2)**shift;a=v*scale
    k=-(-a.numerator//a.denominator) if upper else a.numerator//a.denominator
    return F(k)/scale


@dataclass(frozen=True)
class I:
    lo:F
    hi:F
    def __post_init__(self):
        if self.lo>self.hi:raise ValueError('empty interval')
    @staticmethod
    def point(x):return I(q(x),q(x))
    @staticmethod
    def out(a,b):return I(round_bound(a,False),round_bound(b,True))
    def __add__(self,o):
        o=iv(o);return I.out(self.lo+o.lo,self.hi+o.hi)
    __radd__=__add__
    def __neg__(self):return I(-self.hi,-self.lo)
    def __sub__(self,o):return self+-iv(o)
    def __rsub__(self,o):return iv(o)+-self
    def __mul__(self,o):
        o=iv(o);a=[self.lo*o.lo,self.lo*o.hi,self.hi*o.lo,self.hi*o.hi];return I.out(min(a),max(a))
    __rmul__=__mul__
    def __truediv__(self,o):
        o=iv(o)
        if o.lo<=0<=o.hi:raise ValueError('interval division through zero')
        return self*I.out(1/o.hi,1/o.lo)
    def intersect(self,lo,hi):return I(max(self.lo,q(lo)),min(self.hi,q(hi)))
    def nonnegative(self):return I(max(self.lo,F(0)),self.hi)
    def serialize(self):return [str(self.lo),str(self.hi)]


def iv(x):return x if isinstance(x,I) else I.point(x)


def small_exp(x,complement=False):
    """Alternating Taylor enclosure for 0<=x<=1, exact partial sums."""
    if not 0<=x<=1:raise ValueError('Taylor range')
    total=F(1);term=F(1)
    for k in range(1,49):
        term*=-x/k;total+=term
    lo=total-term*x/49;hi=total
    if complement:return I.out(1-hi,1-lo).intersect(0,1)
    return I.out(lo,hi).intersect(0,1)


def exp_scalar(x,complement=False):
    x=q(x)
    if x<0:raise ValueError('nonnegative exponential argument required')
    if x<=1:return small_exp(x,complement)
    if x>=2*BITS:
        # e>2, so exp(-x)<=2^(-2*BITS). Avoid enormous denominators.
        return I(1-F(1,2**(2*BITS)),F(1)) if complement else I(F(0),F(1,2**(2*BITS)))
    k=max(0,x.numerator.bit_length()-x.denominator.bit_length()+1)
    a=small_exp(x/(2**k))
    for _ in range(k):a=(a*a).intersect(0,1)
    return (1-a).intersect(0,1) if complement else a


def expneg(x):
    x=iv(x)
    return I(exp_scalar(x.hi).lo,exp_scalar(x.lo).hi)


def survival_fraction(x):
    x=iv(x)
    return I(exp_scalar(x.lo,True).lo,exp_scalar(x.hi,True).hi)


def exact_material_prefix(material,cfg,vol):
    """Enclose the exact real prefix on binary geometry/input chart.
    Exact initial D->population conversion; track (do not erase) charge gap.
    Electron and neutral conservation reduce interval dependency growth.
    Field storage upper follows incident and incoming birth kinetic only.
    """
    rows,neutral,D,gyro,axis=material;n=len(rows);kin=cfg['kinetics'];D=np.asarray(D,float)
    h=q(float(cfg['period_s'])/len(cfg['incident_sqrt_W']));horizon=int(cfg['max_cycles']);tail=int(cfg.get('restoration_steps',0))
    if not cfg.get('fixed_horizon',True) or h<=0 or horizon<1 or tail<0 or D.shape!=(n,3) or len(vol)!=n:raise ValueError('prefix chart')
    initial=[[q(D[i,j])*q(MASS[j])/q(CHARGE[j])**2 for j in range(3)] for i in range(n)]
    pool0=[[q(v) for v in row] for row in kin['initial_neutral_m3']]
    if len(pool0)!=n or any(len(p)!=2 for p in pool0) or any(v<0 for row in initial+pool0 for v in row):raise ValueError('initial material chart')
    gap=[p[0]-p[1]-p[2] for p in initial];inventory=[[p[j+1]+r[j] for j in range(2)] for p,r in zip(initial,pool0)]
    pop=[[iv(v) for v in row] for row in initial];pool=[[iv(v) for v in row] for row in pool0];theta=[iv(0) for _ in range(n)]
    alpha,k,g,Q=[list(map(q,kin[name])) for name in ('recombination_m3_s','ionization_s_inv','heater_ionization_per_J','activation_temperature_K')] if 'activation_temperature_K' in kin else [list(map(q,kin[name])) for name in ('recombination_m3_s','ionization_s_inv','heater_ionization_per_J')]+[[F(0),F(0)]]
    if any(len(v)!=2 or min(v)<0 for v in (alpha,k,g,Q)):raise ValueError('reaction coefficients')
    cap=list(map(q,cfg['heat_capacity_J_K']));cool=list(map(q,cfg['cooling_W_K']));V=list(map(q,vol));chem=list(map(q,kin['formation_J_per_particle']))
    birth=np.asarray(kin['birth_velocity_m_s'],float)
    eta=q(kin['chemical_input_efficiency']);rec=q(kin['chemical_recovery_efficiency']);eff=q(cfg['heater_efficiency'])
    if any(len(v)!=n or min(v)<=0 for v in (cap,cool,V)) or len(chem)!=3 or min(chem)<0 or birth.shape!=(n,3,3) or not 0<eta<=1 or not 0<eff<=1 or not 0<=rec<=1:raise ValueError('energy chart')
    heat=np.asarray(cfg['heating_W'],float);src=list(map(q,cfg['incident_sqrt_W']))
    if heat.shape!=(len(src),n) or np.any(heat<0):raise ValueError('heat chart')
    paid=iv(0);birth_work=iv(0);incident=F(0);history=[]
    # Original theta exponential factors are constant, precompute once.
    decay=[expneg(h*cool[i]/cap[i]) for i in range(n)];beta=[survival_fraction(h*cool[i]/cap[i])/cool[i] for i in range(n)]
    half=[expneg(h*cool[i]/(2*cap[i])) for i in range(n)];beta_half=[survival_fraction(h*cool[i]/(2*cap[i]))/cool[i] for i in range(n)]
    steps=[(src[t],heat[t]) for _ in range(horizon) for t in range(len(src))]+[(F(0),np.zeros(n)) for _ in range(tail)]
    for inc,power in steps:
        incident+=h*inc*inc;cost=iv(0);mid=[];events=[]
        for i in range(n):
            old=pop[i];p=q(power[i]);T=theta[i]+q(rows[i]['te'])
            if old[0].lo<0 or T.lo<=0:raise ValueError('electron or temperature interval leaves domain')
            r=[old[j+1]*survival_fraction(old[0]*(h*alpha[j])) for j in range(2)]
            available=[pool[i][j]+r[j] for j in range(2)]
            a=[available[j]*survival_fraction((expneg(iv(Q[j])/T)*k[j]+g[j]*p)*h) for j in range(2)]
            ions=[(old[j+1]-r[j]+a[j]).intersect(0,inventory[i][j]) for j in range(2)]
            electron=gap[i]+ions[0]+ions[1]
            if gap[i]>=0:electron=electron.nonnegative()
            elif electron.lo<0:raise ValueError('nonneutral electron interval leaves domain')
            new=[electron,*ions]
            rr=[r[0]+r[1],*r];aa=[a[0]+a[1],*a]
            bwork=sum((aa[j]*(V[i]*q(MASS[j])*sum((q(v)**2 for v in birth[i,j]),F(0))/2) for j in range(3)),iv(0))
            formed=sum((aa[j]*(V[i]*chem[j]) for j in range(3)),iv(0));removed=sum((rr[j]*(V[i]*chem[j]) for j in range(3)),iv(0))
            birth_work+=bwork;cost+=(bwork+formed)/eta-removed*rec
            events.append(dict(old=[v.serialize() for v in old],removed=[v.serialize() for v in rr],created=[v.serialize() for v in aa]))
            pop[i]=new;pool[i]=[(inventory[i][j]-ions[j]).intersect(0,inventory[i][j]) for j in range(2)]
            mid.append((half[i]*theta[i]+beta_half[i]*p).serialize());theta[i]=decay[i]*theta[i]+beta[i]*p
        paid+=cost+h*sum(map(q,power),F(0))/eff
        history.append(dict(population=[[v.serialize() for v in row] for row in pop],pool=[[v.serialize() for v in row] for row in pool],temperature=[v.serialize() for v in theta],mid_temperature=mid,events=events))
    formation=sum((pop[i][j]*(V[i]*chem[j]) for i in range(n) for j in range(3)),iv(0))
    initial_formation=sum((initial[i][j]*V[i]*chem[j] for i in range(n) for j in range(3)),F(0))
    field_upper=incident+birth_work.hi
    support=[[v.lo>0 for v in row] for row in pop];known=all(v.lo>0 or v.hi==0 for row in pop for v in row)
    return dict(history=history,paid_J=paid.serialize(),birth_work_J=birth_work.serialize(),incident_J=str(incident),
        terminal_formation_J=formation.serialize(),initial_formation_J=str(initial_formation),
        field_energy_upper_J=str(field_upper),population_support=support,support_known=known,
        electron_upper=[str(row[0].hi) for row in pop],temperature_upper=[str(v.hi) for v in theta],
        exact_initial_charge_gap=[str(v) for v in gap],exact_charge_neutral=not any(gap),
        initial_population_zero=not any(v for row in initial for v in row),
        fixed_binary_geometry=True,physical_admission=False)
