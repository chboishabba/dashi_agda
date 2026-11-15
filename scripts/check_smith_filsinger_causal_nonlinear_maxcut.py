#!/usr/bin/env python3
"""Source-qualified nonlinear Smith/Filsinger companion.
No measured environmental gain or actual material coefficient claimed.
For the full 29-test numerical/audio replay see the same-turn zip artifact.
"""
from math import pi, sqrt
import numpy as np
import sympy as sp
from scipy.integrate import solve_ivp

def exact_pump_nonlinear_identity():
    t=sp.symbols("t",real=True)
    x,y,p1,p2=[sp.Function(s)(t) for s in ("x","y","p1","p2")]
    k1,k2,g,lam=[sp.Function(s)(t) for s in ("k1","k2","g","lambda")]
    r1,r2,d,n=sp.symbols("r1 r2 drive natural",real=True)
    H=(p1*p1+p2*p2)/2+k1*x*x/2+k2*y*y/2+g*x*x*y+lam*x**4/4
    substitutions={
      sp.diff(x,t):p1,sp.diff(y,t):p2,
      sp.diff(p1,t):-k1*x-2*g*x*y-lam*x**3-r1*p1+d,
      sp.diff(p2,t):-k2*y-g*x*x-r2*p2+n}
    source=d*p1+n*p2
    heat=r1*p1*p1+r2*p2*p2
    modulation=sp.diff(k1,t)*x*x/2+sp.diff(k2,t)*y*y/2+sp.diff(g,t)*x*x*y+sp.diff(lam,t)*x**4/4
    assert sp.simplify(sp.diff(H,t).subs(substitutions)-source+heat-modulation)==0
    return True

def delayed_wave(samples, dt, flight):
    d=round(flight/dt)
    if abs(d*dt-flight)>1e-10:raise ValueError("flight is not an integer sample shift")
    output=np.zeros_like(np.asarray(samples,dtype=float))
    if d<len(output):output[d:]=np.asarray(samples)[:len(output)-d] if d else np.asarray(samples)
    return output

def finite_source_bounds(useful_watts=.4,earth_ohms=1000.,rf_density=63e-6,efficiency=.63):
    return {"earth_open_circuit_voltage_required":sqrt(4*useful_watts*earth_ohms),
            "effective_rf_aperture_m2_required":useful_watts/(rf_density*efficiency)}

def simulate(phase=0., duration=4., h=.004, drive=4., natural=.16,
             mix=.8, slow_env_hz=1., fast_hz=16., slow_mod=.8):
    # Conservative quadratic mixing potential g*x²*y with stabilizing x⁴.
    wf=2*pi*fast_hz;we=2*pi*slow_env_hz
    k=wf*wf;ke=we*we;g=mix*ke
    quartic=3*g*g/ke  # > 2*g²/ke makes the static polynomial bounded below
    dfast=.15;denv=.14;load=.07
    def f(t,z):
      x,v,y,u=z
      stiffness=k*(1+h*np.cos(2*wf*t+phase))
      fd=drive*(1+slow_mod*np.cos(we*t/2+phase))*np.cos(wf*t)
      fn=natural*np.cos(we*t+.37)
      return [v,-stiffness*x-2*g*x*y-quartic*x**3-dfast*v+fd,
              u,-ke*y-g*x*x-denv*u+fn]
    sol=solve_ivp(f,[0,duration],[.001,0.,.001,0.],rtol=2e-8,atol=2e-10,
                  max_step=.001,t_eval=np.linspace(0,duration,round(duration/.002)+1))
    if not sol.success:raise RuntimeError(sol.message)
    t=sol.t;x,v,y,u=sol.y
    stiff=k*(1+h*np.cos(2*wf*t+phase))
    U=.5*(v*v+u*u+stiff*x*x+ke*y*y)+g*x*x*y+quartic*x**4/4
    wd=np.trapezoid(drive*(1+slow_mod*np.cos(we*t/2+phase))*np.cos(wf*t)*v,t)
    wn=np.trapezoid(natural*np.cos(we*t+.37)*u,t)
    wp=np.trapezoid(-wf*k*h*np.sin(2*wf*t+phase)*x*x,t)
    useful=np.trapezoid(load*v*v,t)
    heat=np.trapezoid((dfast-load)*v*v+denv*u*u,t)
    stored=U[-1]-U[0]
    return {"phase":phase,"driver":float(wd),"natural":float(wn),
            "modulator":float(wp),"useful":float(useful),"heat":float(heat),
            "storage_change":float(stored),
            "work_residual":float(stored-wd-wn-wp+useful+heat)}

def tests():
    assert exact_pump_nonlinear_identity()
    r=finite_source_bounds()
    assert abs(r["earth_open_circuit_voltage_required"]-40)<1e-10
    assert abs(r["effective_rf_aperture_m2_required"]-10078.1053162)<1e-4
    x=delayed_wave([1]+[0]*10,.01,.03)
    assert all(x[:3]==0) and x[3]==1
    vals=[simulate(p,duration=2) for p in (0,pi/2,pi,3*pi/2)]
    assert all(abs(v["work_residual"])<.003 for v in vals),vals
    assert np.ptp([v["modulator"] for v in vals])>.1
    assert np.ptp([v["natural"] for v in vals])>0
    assert simulate(natural=0.,duration=1)["natural"]==0.
    return vals

if __name__=="__main__":
    for item in tests():print(item)
    print("PASS: conditional source work, causal delay and exact pumped Hamiltonian")
