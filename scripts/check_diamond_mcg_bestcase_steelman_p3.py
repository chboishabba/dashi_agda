#!/usr/bin/env python3
"""Best-case (maximum eigenvalue) diamond array fixture, not worst-case.

Two independent-resource macro groups share a fixed total budget. Under this
synthetic photon-splitting law N=100 and N=1000 yield identical group variance.
Free-space dipole geometry; correlated ambient 2D magnetic field; uncalibrated.
"""
import json
import numpy as np
import sympy as s
from scipy.optimize import differential_evolution

def exact_checks():
    r, v, t, a = s.symbols('r v t a', positive=True)
    D=s.diag(-1/r**3,-1/r**3,2/r**3)
    assert D.T*D == s.diag(r**-6,r**-6,4/r**6)
    C=s.Matrix([[2*v+t*t,t*t],[t*t,2*v+t*t]])
    assert s.simplify((s.Matrix([[a,a]])*C.inv()*s.Matrix([a,a]))[0]-a*a/(v+t*t))==0
    assert s.simplify((s.Matrix([[a,-a]])*C.inv()*s.Matrix([a,-a]))[0]-a*a/v)==0
    for n in (100,1000):
        assert s.cancel(n*a*a/(n*v)-a*a/v)==0

def response(x,angle,source_x,r):
    axis=np.array([np.sin(angle),0,np.cos(angle)])
    delta=np.array([source_x-x,0,r])
    d=np.linalg.norm(delta);u=delta/d
    return axis@(3*np.outer(u,u)-np.eye(3))/d**3,axis[[0,2]]

def information(params,r,h,tau,cone):
    x1,x2,a1,a2=params[:4]
    sx=params[4] if cone else 0.
    vecs=[response(x,a,sx,r) for x,a in [(x1,a1),(x2,a2)]]
    S=np.stack([v[0] for v in vecs])
    A=np.stack([v[1] for v in vecs])
    C=2*np.eye(2)+tau*tau*A@A.T
    F=S.T@np.linalg.solve(C,S)
    return float(np.linalg.eigvalsh((F+F.T)/2)[-1])

def optimize(r,h,tau,cone=0):
    bounds=[(-h,h),(-h,h),(0,2*np.pi),(0,2*np.pi)]
    if cone: bounds.append((-r*np.tan(np.deg2rad(cone)),
                             r*np.tan(np.deg2rad(cone))))
    res=differential_evolution(lambda x:-information(x,r,h,tau,cone),
             bounds,seed=18,maxiter=90,popsize=10,tol=1e-9,polish=True)
    sx=res.x[4] if cone else 0.
    nearest=np.sqrt(r*r+max(0,abs(sx)-h)**2)
    bound=4/nearest**6
    value=information(res.x,r,h,tau,cone)
    assert 0<=value<=bound*(1+1e-10)
    return dict(range_m=r,aperture_diameter_m=2*h,
        ambient_to_independent_std_ratio=tau,cone_half_angle_deg=cone,
        feasible_best_information=value,ideal_upper_bound=bound,
        achievable_fraction_of_ideal_upper=value/bound,
        sensor_x_positions_m=list(map(float,res.x[:2])),
        sensor_axis_angles_rad=list(map(float,res.x[2:4])),
        source_x_m=float(sx),optimizer_converged=bool(res.success),
        globally_certified_optimum=bool(tau==0 and abs(value-bound)<1e-9*bound))

def main():
    exact_checks()
    cases=[(2.,.25,0.,0.),(2.,.25,10.,0.),
           (10.,.25,0.,0.),(10.,.25,10.,0.),
           (10.,.25,10.,20.),(100.,.25,10.,0.)]
    rows=[optimize(*c) for c in cases]
    assert rows[0]['globally_certified_optimum']
    assert rows[2]['globally_certified_optimum']
    for row in rows:
        print("BEST-CASE",json.dumps(row))
    print("PASS exact SymPy controls and bounded best-case design fixtures")
    print("SCOPE: no measured NV noise, heart current, phase-tracking or false alarms")
    print(json.dumps(dict(schema="diamond-mcg-p3-bestcase-v1",
       mode="MAX over dipole moment, sensor axes, two grouped positions and optional source bearing",
       resource="fixed total, exact N=100/1000 invariance for identical groups",
       experimental_validation=False,rows=rows),indent=2))

if __name__=="__main__":main()
