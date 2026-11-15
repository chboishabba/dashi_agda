"""DASHI standalone constrained drive optimisation; no actual manufacturer circuit.

Linear fixed-inductance PM winding model. Optimises a convex copper/slew
surrogate under exact sampled torque, current and terminal-voltage constraints.
Bus efficiency is then evaluated with explicit conventional loss assumptions.
A copper/slew optimum is NOT globally bus-efficiency optimal.
Requires numpy and scipy.
"""
from dataclasses import dataclass, replace
import numpy as np
from scipy.optimize import minimize
import json

@dataclass(frozen=True)
class Motor:
    R: float = 1.5
    L: float = .02
    K: float = .06
    speed: float = 100.
    torque: float = .015
    bus: float = 24.
    imax: float = 2.
    eta_forward: float = .97
    eta_reverse: float = .97
    idle_w: float = .15
    switch_hz: float = 20000.
    switch_energy_j: float = 2e-6
    switch_energy_per_a_j: float = 1e-6
    core_loss_w: float = .05

def model(m, n):
    theta = np.arange(n) * 2*np.pi/n
    k = m.K*np.sin(theta)
    D = np.zeros((n,n))
    for j in range(n):
        D[j,(j+1)%n] = 0.5
        D[j,(j-1)%n] = -0.5
    D /= 2*np.pi/n
    V = m.R*np.eye(n) + m.L*m.speed*D
    return k, D, V, m.speed*k

def copper_reference(m, k, bipolar):
    lower = -m.imax if bipolar else 0.
    def i(lam): return np.clip(lam*k, lower, m.imax)
    lo,hi=0.,1.
    while np.mean(k*i(hi))<m.torque:
        hi*=2.
        if hi>1e15: raise ValueError("infeasible torque")
    for _ in range(80):
        mid=(lo+hi)/2
        if np.mean(k*i(mid))<m.torque:lo=mid
        else:hi=mid
    return i(hi)

def assess(m, i, k, D, V, emf):
    terminal = V@i + emf
    electrical = terminal*i
    positive = float(np.mean(np.maximum(electrical,0)))
    negative = float(np.mean(np.maximum(-electrical,0)))
    shaft = m.speed*float(np.mean(k*i))
    copper = m.R*float(np.mean(i*i))
    switching = m.switch_hz*(m.switch_energy_j
                             +m.switch_energy_per_a_j*float(np.mean(abs(i))))
    bus = (positive/m.eta_forward - m.eta_reverse*negative
           +m.idle_w+switching+m.core_loss_w)
    result = dict(shaft_w=shaft, bus_w=bus, efficiency=shaft/bus,
                  copper_w=copper, switching_w=switching,
                  core_w=m.core_loss_w, idle_w=m.idle_w,
                  voltage_peak_v=float(max(abs(terminal))),
                  current_peak_a=float(max(abs(i))),
                  gross_regeneration_w=negative,
                  energy_residual_w=float(np.mean(electrical)-shaft-copper),
                  magnetic_period_residual_w=float(np.mean(i*(m.L*m.speed*(D@i)))))
    return result

def optimize(m=Motor(), n=81, bipolar=False, slew_penalty=0.):
    if n<9 or min(m.R,m.L,m.K,m.speed,m.bus,m.imax)<=0:
        raise ValueError("invalid model parameters")
    if not 0<m.eta_forward<=1 or not 0<m.eta_reverse<=1:
        raise ValueError("invalid conversion efficiency")
    k,D,V,emf=model(m,n)
    reference=copper_reference(m,k,bipolar)
    Q=m.R*np.eye(n)/n + slew_penalty*(D.T@D)/n
    def obj(i):return float(i@Q@i)
    torque_row=k/n
    constraints=[
        dict(type="eq",fun=lambda i:np.dot(torque_row,i)-m.torque,
             jac=lambda i:torque_row),
        dict(type="ineq",fun=lambda i:np.r_[m.bus-emf-V@i,m.bus+emf+V@i],
             jac=lambda i:np.vstack((-V,V)))
    ]
    lower = -m.imax if bipolar else 0.
    res=minimize(obj,reference,jac=lambda i:2*Q@i,
                 bounds=[(lower,m.imax)]*n,constraints=constraints,
                 method="SLSQP",options=dict(ftol=1e-11,maxiter=300))
    if not res.success:raise RuntimeError(res.message)
    out=assess(m,res.x,k,D,V,emf)
    assert abs(np.mean(k*res.x)-m.torque)<1e-7
    assert out["voltage_peak_v"] <= m.bus+1e-6
    assert out["current_peak_a"] <= m.imax+1e-6
    assert abs(out["energy_residual_w"]) < 1e-9
    assert abs(out["magnetic_period_residual_w"]) < 1e-9
    out["copper_reference_w"]=m.R*float(np.mean(reference*reference))
    out["slew_penalty"]=slew_penalty
    return out

def test():
    cases={}
    for m in (Motor(),replace(Motor(),speed=250.,bus=12.)):
        for bipolar in (False,True):
            for penalty in (0.,2.):
                x=optimize(m,81,bipolar,penalty)
                assert x["bus_w"]>=x["shaft_w"]
                cases[f"speed={m.speed}_bus={m.bus}_bipolar={bipolar}_slew={penalty}"]=x
    for n in (27,81):
        for bipolar in (False,True):
            x=optimize(Motor(),n,bipolar)
            assert abs(x["copper_w"]-x["copper_reference_w"])<1e-6
    return dict(status="passed",cases=cases)

if __name__=="__main__":
    print(json.dumps(test(),indent=2))
