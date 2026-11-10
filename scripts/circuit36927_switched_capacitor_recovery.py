"""Independent low-voltage mathematical capacitor-transfer model.

Two capacitors connected to common reference via a switched series resistor.
Implicit Euler advances the capacitor voltages and records resistor heat,
capacitor energy change and method numerical dissipation separately.
No third-party wiring or energy harvesting assertion is encoded.
"""
from dataclasses import dataclass
from math import isclose, isfinite
import random

@dataclass(frozen=True)
class TransferState:
    v1: float
    v2: float

@dataclass(frozen=True)
class TransferStep:
    state: TransferState
    i12: float
    old_energy: float
    new_energy: float
    resistor_heat: float
    discretization_loss: float
    balance_residual: float
    switch_closed: bool

def energy(c1: float, c2: float, state: TransferState) -> float:
    return 0.5 * (c1 * state.v1 ** 2 + c2 * state.v2 ** 2)

def transfer_step(c1: float, c2: float, r: float, dt: float,
                  state: TransferState, closed: bool) -> TransferStep:
    vals = (c1, c2, r, dt, state.v1, state.v2)
    if not all(isfinite(x) for x in vals) or min(c1,c2,r,dt) <= 0:
        raise ValueError("positive finite C1, C2, R, timestep required")
    old_e = energy(c1, c2, state)
    if not closed:
        return TransferStep(state, 0., old_e, old_e, 0., 0., 0., False)
    # Charge: C1 dv1/dt = -i, C2 dv2/dt = +i;
    # implicit Ohm: i = (v1_new - v2_new)/r.
    i = (state.v1-state.v2)/(r + dt*(1/c1 + 1/c2))
    v1 = state.v1 - dt*i/c1
    v2 = state.v2 + dt*i/c2
    new = TransferState(v1,v2)
    new_e = energy(c1,c2,new)
    heat = dt*r*i*i
    artificial = 0.5*c1*(v1-state.v1)**2 + 0.5*c2*(v2-state.v2)**2
    residual = old_e-new_e-heat-artificial
    return TransferStep(new,i,old_e,new_e,heat,artificial,residual,True)

def test() -> dict:
    c1,c2,r,dt = 100e-6,100e-6,10.,1e-4
    state=TransferState(12.,0.)
    initial_energy=energy(c1,c2,state)
    transferred_heat=0.;method_loss=0.
    for k in range(2000):
        x=transfer_step(c1,c2,r,dt,state,closed=(k!=0))
        assert abs(x.balance_residual)<1e-12
        assert x.new_energy<=x.old_energy+1e-12
        assert x.resistor_heat>=0 and x.discretization_loss>=0
        assert abs(c1*(x.state.v1-state.v1)+c2*(x.state.v2-state.v2))<1e-15
        if k==0: assert x.state==state and x.i12==0
        transferred_heat+=x.resistor_heat
        method_loss+=x.discretization_loss
        state=x.state
    assert abs(state.v1-6.)<1e-8 and abs(state.v2-6.)<1e-8
    assert isclose(initial_energy,energy(c1,c2,state)+transferred_heat+method_loss,abs_tol=1e-12)
    random.seed(36927)
    random_cases=0
    for _ in range(200):
        c1=10**random.uniform(-8,-3);c2=10**random.uniform(-8,-3)
        r=10**random.uniform(-1,4);dt=10**random.uniform(-9,-3)
        old=TransferState(random.uniform(-20,20),random.uniform(-20,20))
        x=transfer_step(c1,c2,r,dt,old,True)
        assert abs(x.balance_residual)<1e-9*max(1.,x.old_energy)
        assert x.new_energy<=x.old_energy+1e-10
        assert isclose(c1*old.v1+c2*old.v2,c1*x.state.v1+c2*x.state.v2,rel_tol=1e-10,abs_tol=1e-11)
        random_cases+=1
    for bad in (0.,-1.,float("nan")):
        try:
            transfer_step(bad,1e-6,10.,1e-4,TransferState(1,0),True)
            raise AssertionError("bad capacitance accepted")
        except ValueError: pass
    return dict(initial_energy_joules=initial_energy,
                final_energy_joules=energy(100e-6,100e-6,state),
                resistor_heat_joules=transferred_heat,
                numerical_loss_joules=method_loss,
                closed_steps=1999,randomized_cases=random_cases,status="passed")

if __name__=="__main__":
    import json
    print(json.dumps(test(),indent=2))
