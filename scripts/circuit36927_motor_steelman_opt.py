"""DASHI-original steelman PM impulse motor; NOT a Resonate369 schematic.

Single-coil constant-L, sinusoidal PM flux gradient, constant speed.
The convex copper-loss optimum follows clipping of lambda*k(theta) for
a fixed mean torque. Drive bus energy includes reversible pin power,
a forward/reverse converter-efficiency model and idle overhead.
The periodic central difference has exactly zero net L*I*dI/dt term.
No anomalous power, no original CAD, and no vendor files are implied.
"""
from dataclasses import dataclass, replace, asdict
from math import pi
import numpy as np
import json

@dataclass(frozen=True)
class Motor:
    R: float = 1.5
    L: float = .02
    K: float = .06
    omega: float = 100.
    torque: float = .015
    bus_v: float = 24.
    imax: float = 2.
    eta: float = .97
    idle_w: float = .15

def optimum(theta, m, bipolar):
    k=m.K*np.sin(theta)
    lower=-m.imax if bipolar else 0.
    def candidate(a): return np.clip(a*k,lower,m.imax)
    def torque(a): return np.mean(k*candidate(a))
    hi=1.
    while torque(hi)<m.torque:
        hi*=2
        if hi>1e15: raise ValueError("torque infeasible")
    lo=0.
    for _ in range(100):
        mid=(lo+hi)/2
        if torque(mid)<m.torque: lo=mid
        else: hi=mid
    return candidate(hi)

def assess(theta,i,m):
    d=2*pi/len(theta)
    didtheta=(np.roll(i,-1)-np.roll(i,1))/(2*d)
    # v = Ri+L di/dt+ omega*d(psi_PM)/d(theta);
    # tau = i*d(psi_PM)/d(theta), with psi_PM = -K*cos(theta).
    emf=m.K*m.omega*np.sin(theta)
    v=m.R*i+m.L*m.omega*didtheta+emf
    pin=v*i
    shaft=np.mean(m.K*i*np.sin(theta))*m.omega
    copper=np.mean(m.R*i*i)
    pos=np.mean(np.maximum(pin,0))
    neg=np.mean(np.maximum(-pin,0))
    bus=pos/m.eta-m.eta*neg+m.idle_w
    return dict(torque_nm=float(shaft/m.omega),shaft_w=float(shaft),
        copper_w=float(copper),pin_w=float(np.mean(pin)),
        bus_w=float(bus),efficiency=float(shaft/bus),
        gross_regen_w=float(neg),gross_import_w=float(pos),
        max_abs_v=float(np.max(np.abs(v))),max_abs_i=float(np.max(np.abs(i))),
        balance_residual_w=float(np.mean(pin)-shaft-copper))

def compare(n=243,m=Motor()):
    assert n>=9 and m.R>0 and m.L>0 and m.K>0 and m.omega>0
    assert 0<m.eta<=1 and m.bus_v>0 and m.imax>0
    th=2*pi*np.arange(n)/n
    positive=np.maximum(np.sin(th),0)
    designs={'optimal_unipolar':optimum(th,m,False),
             'optimal_bipolar':optimum(th,m,True)}
    for name,power in [('broad_pulse',2),('narrow_pulse',6)]:
        shape=positive**power
        designs[name]=shape*m.torque/(m.K*np.mean(np.sin(th)*shape))
    out={name:assess(th,i,m) for name,i in designs.items()}
    for name,res in out.items():
        assert abs(res['torque_nm']-m.torque)<1e-10,name
        assert abs(res['balance_residual_w'])<1e-10,name
        assert res['max_abs_i']<=m.imax+1e-8,name
        assert res['max_abs_v']<=m.bus_v+1e-8,name
        assert res['bus_w']>=res['shaft_w'],name
    assert out['optimal_bipolar']['copper_w']<=out['optimal_unipolar']['copper_w']+1e-10
    for name in ['broad_pulse','narrow_pulse']:
        assert out['optimal_unipolar']['copper_w']<=out[name]['copper_w']+1e-10
    return out

def voltage_limited_speed(m=Motor(),n=243):
    th=2*pi*np.arange(n)/n
    result={}
    for bipolar in (False,True):
        i=optimum(th,m,bipolar)
        lo,hi=0.,10000.
        for _ in range(75):
            mid=(lo+hi)/2
            if assess(th,i,replace(m,omega=mid))['max_abs_v']<=m.bus_v:lo=mid
            else:hi=mid
        x=assess(th,i,replace(m,omega=lo))
        result['bipolar' if bipolar else 'unipolar']=dict(
            speed_rad_s=float(lo),rpm=float(lo*60/(2*pi)),
            shaft_w=x['shaft_w'],bus_w=x['bus_w'],efficiency=x['efficiency'])
    return result

def test():
    models={n:compare(n) for n in (27,81,243,729)}
    sensitivities={}
    for r in (.5,1.5,3.):
        for eta in (.9,.97,.99):
            x=compare(m=replace(Motor(),R=r,eta=eta))
            sensitivities[f"R={r} eta={eta}"]={
                "unipolar_eta":x['optimal_unipolar']['efficiency'],
                "bipolar_eta":x['optimal_bipolar']['efficiency']}
    return dict(assumptions=asdict(Motor()),comparison=models[243],
        sectors_tested=list(models),sensitivities=sensitivities,
        voltage_limited_speed=voltage_limited_speed(),status='passed')
if __name__=='__main__':print(json.dumps(test(),indent=2))
