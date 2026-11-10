"""Bus-power optimisation on the independent DASHI constrained motor model.

SLSQP searches a nonsmooth, generally nonconvex converter objective. Returned
solution is a *locally improved feasible candidate*, NOT a globally proved
optimum. No source-specific Holmstrom motor values are asserted.
"""
import json
from dataclasses import replace
import numpy as np
from scipy.optimize import minimize
from circuit36927_joint_voltage_constrained_drive import Motor, model, copper_reference, optimize, assess

def optimize_bus(m=Motor(), n=81, bipolar=False):
    k,D,V,emf = model(m,n)
    ref=copper_reference(m,k,bipolar)
    tau_row=k/n
    lo=-m.imax if bipolar else 0.
    def objective_and_gradient(i):
        terminal=V@i+emf
        pin=terminal*i
        weights=np.where(pin>=0,1./m.eta_forward,m.eta_reverse)
        smooth_abs=np.sqrt(i*i+1e-12)
        switch=m.switch_hz*(m.switch_energy_j
                            +m.switch_energy_per_a_j*np.mean(smooth_abs))
        value=(float(np.dot(weights,pin))/n
               +m.idle_w+m.core_loss_w+switch)
        grad=(weights*terminal+V.T@(weights*i))/n
        grad+=m.switch_hz*m.switch_energy_per_a_j*i/smooth_abs/n
        return value,grad
    constraints=[
      dict(type="eq",fun=lambda i:float(np.dot(tau_row,i)-m.torque),
           jac=lambda i:tau_row),
      dict(type="ineq",
           fun=lambda i:np.r_[m.bus-emf-V@i,m.bus+emf+V@i],
           jac=lambda i:np.vstack((-V,V)))
    ]
    solution=minimize(lambda i:objective_and_gradient(i)[0],ref,
       jac=lambda i:objective_and_gradient(i)[1],method="SLSQP",
       bounds=[(lo,m.imax)]*n,constraints=constraints,
       options=dict(ftol=1e-10,maxiter=250))
    if not solution.success:raise RuntimeError(solution.message)
    actual=assess(m,solution.x,k,D,V,emf)
    assert abs(float(np.mean(k*solution.x))-m.torque)<1e-7
    assert actual["voltage_peak_v"]<=m.bus+1e-6
    assert actual["current_peak_a"]<=m.imax+1e-6
    assert abs(actual["energy_residual_w"])<1e-9
    assert abs(actual["magnetic_period_residual_w"])<1e-9
    candidate=optimize(m,n,bipolar,0.)
    assert actual["bus_w"]<=candidate["bus_w"]+1e-5
    return dict(bus_candidate=actual, copper_candidate=candidate,
        local_bus_improvement_fraction=
          (candidate["bus_w"]-actual["bus_w"])/candidate["bus_w"])

def test():
    output={}
    for m in (Motor(),replace(Motor(),speed=250.,bus=12.)):
        for bipolar in (False,True):
            case=f"speed={m.speed}_bus={m.bus}_bipolar={bipolar}"
            output[case]=optimize_bus(m,81,bipolar)
    return dict(status="passed",cases=output,global_optimality_proved=False)

if __name__=="__main__":print(json.dumps(test(),indent=2))
