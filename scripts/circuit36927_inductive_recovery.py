"""Independent DASHI steelman pulse-recovery model (not a manufacturer's circuit).

An ideal current-commutated inductor delivers its stored energy into a
capacitor through an ideal rectifier/active switch. Optional series R models
winding, conductor and semiconductor conduction. We separate lossless exact
solutions from dissipative implicit-midpoint steps and account for energy.
No anomalous energy claims, vendor designs, or high-voltage build directions.
"""
from dataclasses import dataclass
from math import atan2, cos, isfinite, pi, sin, sqrt
from random import Random

@dataclass(frozen=True)
class State:
    current_a: float
    capacitor_v: float

@dataclass(frozen=True)
class Components:
    inductance_h: float
    capacitance_f: float
    series_ohms: float = 0.0

    def validate(self):
        if not all(isfinite(x) for x in (self.inductance_h, self.capacitance_f, self.series_ohms)):
            raise ValueError('finite parameters required')
        if self.inductance_h <= 0 or self.capacitance_f <= 0 or self.series_ohms < 0:
            raise ValueError('L,C positive and R nonnegative required')


def energy(parts: Components, state: State) -> float:
    parts.validate()
    if not all(isfinite(x) for x in (state.current_a, state.capacitor_v)):
        raise ValueError('finite state required')
    return .5*parts.inductance_h*state.current_a**2 + .5*parts.capacitance_f*state.capacitor_v**2


def ideal_diode_capture(parts: Components, initial: State):
    """Ideal first current zero, no reverse conduction; I0>0 and V0>=0.

    Current moves from coil to capacitor: L dI/dt=-V, C dV/dt=I.
    Returned final storage equals initial capacitor + inductor storage.
    """
    parts.validate()
    if parts.series_ohms != 0 or initial.current_a <= 0 or initial.capacitor_v < 0:
        raise ValueError('ideal diode capture needs R=0, positive initial I, V>=0')
    impedance = sqrt(parts.inductance_h/parts.capacitance_f)
    omega = 1/sqrt(parts.inductance_h*parts.capacitance_f)
    angle = atan2(impedance*initial.current_a, initial.capacitor_v)
    time_to_zero = angle/omega
    final = State(0.0, sqrt(initial.capacitor_v**2 + (impedance*initial.current_a)**2))
    assert abs(energy(parts, initial)-energy(parts,final)) < 1e-11*max(1,energy(parts,initial))
    return time_to_zero, final


def midpoint_step(parts: Components, initial: State, dt: float):
    """Implicit midpoint for closed RLC recovery interval.

    Exactly (to floating tolerance): E_old - E_new = dt*R*I_mid**2.
    Unlike backward Euler, midpoint has no artificial LC damping.
    Caller is responsible for switching/diode zero-current events.
    """
    parts.validate()
    if not isfinite(dt) or dt <= 0:
        raise ValueError('positive finite timestep required')
    L,C,R = parts.inductance_h,parts.capacitance_f,parts.series_ohms
    a=dt/(2*L)
    b=dt/(2*C)
    # I_new = I_old - dt/L*(R*(I_old+I_new)/2 + (V_old+V_new)/2)
    # V_new = V_old + dt/C*(I_old+I_new)/2
    det=1+a*R+a*b
    i_new=((1-a*R-a*b)*initial.current_a-2*a*initial.capacitor_v)/det
    v_new=initial.capacitor_v+b*(initial.current_a+i_new)
    final=State(i_new,v_new)
    i_mid=(initial.current_a+i_new)/2
    heat=dt*R*i_mid*i_mid
    residual=energy(parts, initial)-energy(parts,final)-heat
    return final,heat,residual


def test():
    # Ideal 10 mH / 100 uF recovery of 2 A into an initially empty cap.
    parts=Components(.01,100e-6)
    initial=State(2,0)
    t,final=ideal_diode_capture(parts,initial)
    assert abs(t-pi/2*sqrt(.01*100e-6))<1e-14
    assert abs(final.capacitor_v-20)<1e-12
    assert abs(energy(parts,initial)-.02)<1e-12
    # Lossless midpoint: negligible drift across many timesteps.
    state=initial
    for _ in range(1000):
        state,heat,residual=midpoint_step(parts,state,1e-6)
        assert heat==0
        assert abs(residual)<1e-12
    assert abs(energy(parts,initial)-energy(parts,state))<1e-11
    # Resistive passive recovery: node power storage decrease is heat.
    lossy=Components(.01,100e-6,1.0)
    state=initial;total_heat=0
    for _ in range(1000):
        state,heat,residual=midpoint_step(lossy,state,1e-6)
        assert heat>=0
        assert abs(residual)<1e-12
        total_heat+=heat
    assert abs(energy(lossy,initial)-energy(lossy,state)-total_heat)<1e-10
    rng=Random(36927)
    for _ in range(500):
        p=Components(10**rng.uniform(-5,-1),10**rng.uniform(-8,-3),rng.uniform(0,20))
        s=State(rng.uniform(-5,5),rng.uniform(-50,50))
        dt=min(1e-5,.05*sqrt(p.inductance_h*p.capacitance_f))
        nxt,heat,res=midpoint_step(p,s,dt)
        assert heat>=0 and abs(res)<1e-9*max(1,energy(p,s))
        assert energy(p,nxt)<=energy(p,s)+1e-9
    for bad in (Components(0,1e-6),Components(.01,0),Components(.01,1e-6,-1)):
        try: energy(bad,initial);raise AssertionError('invalid components accepted')
        except ValueError: pass
    return dict(ideal_initial_energy_j=.02,ideal_captured_voltage_v=final.capacitor_v,
                ideal_capture_time_s=t,lossy_final_energy_j=energy(lossy,state),
                loss_heat_j=total_heat,randomised_midpoint_cases=500,status='passed')

if __name__=='__main__':
    import json
    print(json.dumps(test(),indent=2))
