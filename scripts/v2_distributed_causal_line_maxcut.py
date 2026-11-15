#!/usr/bin/env python3
"""Exact discrete wave-power ledger and analytic 1D telegrapher laws.

Mathematical *model*, not original V2 wiring or measurement. Packets encode
lossless matched/reflective 1D transmission lines; per-hop amplitude attenuation
accounts for passive distributed loss without allowing pre-arrival signals.
Each step and port is signed from a COMMON clock. Avoids a fake one-RK-step
cable delay in the 142-us V2 controller: physical flights can be nanoseconds.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction
import json
import math
import numpy as np
import sympy as sp

C0 = 299_792_458.0


@dataclass(frozen=True)
class CausalLine:
    length_m: float = 0.5
    front_speed_m_s: float = 0.7*C0
    impedance_ohm: float = 50.0
    load_reflection: float = 0.0
    source_reflection: float = 0.0
    amplitude_survival_per_tick: float = 1.0

    def validate(self):
        if not (0 < self.length_m and 0 < self.front_speed_m_s <= C0):
            raise ValueError('finite separated path must have 0 < front speed <= c')
        if self.impedance_ohm <= 0:
            raise ValueError('positive characteristic impedance required')
        if not (abs(self.load_reflection) <= 1 and abs(self.source_reflection) <= 1):
            raise ValueError('passive reflections require magnitude <= 1')
        if not (0 <= self.amplitude_survival_per_tick <= 1):
            raise ValueError('passive line cannot amplify an incident packet')

    @property
    def flight_s(self):
        self.validate()
        return self.length_m/self.front_speed_m_s


def telegrapher_identity():
    """Continuum pointwise Poynting balance; exact symbolic substitution.

    ∂x V = -L'∂t I-R'I, ∂x I = -C'∂t V-G'V
    ∂t .5(C'V²+L'I²)+∂x(VI)=-R'I²-G'V².
    Positive L',C' wavefront v=1/sqrt(L'C'); v<=c separately required.
    """
    t,x=sp.symbols('t x', real=True)
    L,C,R,G=sp.symbols('L C R G', positive=True)
    V,I=sp.Function('V')(x,t),sp.Function('I')(x,t)
    E=sp.Rational(1,2)*(C*V**2+L*I**2)
    flux=V*I
    eq=sp.diff(E,t)+sp.diff(flux,x)+R*I**2+G*V**2
    substituted=sp.expand(eq.subs({sp.diff(V,t):-(sp.diff(I,x)+G*V)/C,
                                    sp.diff(I,t):-(sp.diff(V,x)+R*I)/L}))
    assert sp.simplify(substituted)==0
    Z=sp.sqrt(L/C)
    speed=1/sp.sqrt(L*C)
    Wp,Wm=sp.symbols('Wp Wm', real=True)
    vs=(Wp+Wm)/2
    ins=(Wp-Wm)/(2*Z)
    assert sp.simplify((vs*ins)-(Wp**2-Wm**2)/(4*Z))==0
    assert sp.simplify((C*vs**2+L*ins**2)/2-C*(Wp**2+Wm**2)/4)==0
    return {'identity':'d_t U + d_x(VI) = -Rprime*I^2 - Gprime*V^2',
            'symbolic_residual':'0',
            'traveling_wave_power':'(Wplus^2-Wminus^2)/(4*Z)',
            'wavefront_speed':'1/sqrt(Lprime*Cprime)',
            'speed_admission':'Lprime*Cprime >= 1/c^2 required for this nondispersive physical model'}


def traveling_packets(line:CausalLine, incident, cells:int, *, dt_s:float|None=None):
    """Energy-conserving two-direction discrete line with passive boundaries.

    Time t: incoming drive is a forward *voltage-wave amplitude* at source.
    A reflection from source can interfere with the drive. P_source is therefore
    NET signed incident-minus-returning power, not merely drive**2.
    On a tick old packet fields propagate/attenuate, reach either boundary,
    reflect, and a new source packet enters. Enew-Eold=P_source-P_load-Q_line.
    This is a delay-line model, not a dispersive/real-material Maxwell solve.
    """
    line.validate()
    if cells < 1: raise ValueError('at least one spatial delay cell required')
    dt=line.flight_s/cells if dt_s is None else float(dt_s)
    if not math.isclose(cells*dt,line.flight_s,rel_tol=1e-10,abs_tol=1e-18):
        raise ValueError('the clock must resolve the exact flight as cells * dt')
    incident=list(incident)
    if len(incident)==0:raise ValueError('nonempty sampled wave required')
    f=[0]*cells
    b=[0]*cells
    factor=dt/(4*line.impedance_ohm)
    r,gs,gl=line.amplitude_survival_per_tick,line.source_reflection,line.load_reflection
    total_source=total_load=total_heat=0
    first_load=None
    trace=[]
    for tick,drive in enumerate(incident):
        before=factor*sum(q*q for q in f+b)
        arrived_right=r*f[-1]
        arrived_left=r*b[-1]
        new_forward=drive+gs*arrived_left
        reflected_left=gl*arrived_right
        f=[new_forward]+[r*q for q in f[:-1]]
        b=[reflected_left]+[r*q for q in b[:-1]]
        after=factor*sum(q*q for q in f+b)
        source=factor*(new_forward**2-arrived_left**2)
        loaded=factor*(arrived_right**2-reflected_left**2)
        dissipated=(1-r*r)*before
        residual=(after-before)-(source-loaded-dissipated)
        if first_load is None and arrived_right != 0:
            first_load=tick
        total_source+=source
        total_load+=loaded
        total_heat+=dissipated
        trace.append(dict(tick=tick,source_energy_j=source,load_energy_j=loaded,
                          line_loss_j=dissipated, stored_energy_j=after,
                          forward_arrival=arrived_right,backward_arrival=arrived_left,
                          energy_residual_j=residual))
    return dict(parameters=asdict(line),dt_s=dt,cells=cells,
                first_forward_arrival_tick=first_load,
                first_forward_arrival_s=None if first_load is None else first_load*dt,
                source_work_j=total_source,load_work_j=total_load,
                dissipated_work_j=total_heat,initial_stored_j=0,
                final_stored_j=trace[-1]['stored_energy_j'],
                energy_residual_j=total_source-total_load-total_heat-trace[-1]['stored_energy_j'],
                max_tick_residual_j=max(abs(v['energy_residual_j']) for v in trace),
                trace=trace)


def exact_fraction_certificate():
    """Use fractions to prove an exact finite two-boundary reflection example.
    No rounding or quadrature. Both incident and returned signed source work.
    """
    line=CausalLine(length_m=7,front_speed_m_s=7,impedance_ohm=2,
                    load_reflection=Fraction(1,2),source_reflection=Fraction(-1,3),
                    amplitude_survival_per_tick=Fraction(3,4))
    # Exact time discretization, 7 cells (1/7 s each) and a rational drive.
    # Floating dt from the physical-value front speed does not enter arithmetic;
    # use a one-unit energy factor (equivalent to common positive dt/4Z).
    cells=7; f=[Fraction(0)]*cells;b=f.copy()
    gs=line.source_reflection;gl=line.load_reflection;r=line.amplitude_survival_per_tick
    source=load=heat=Fraction(0)
    for t in range(42):
        old=sum(q*q for q in f+b)
        fr=r*f[-1];br=r*b[-1]
        a=(Fraction(3,2) if t==0 else Fraction(-1,5) if t==9 else Fraction(0))+gs*br
        rr=gl*fr
        f=[a]+[r*q for q in f[:-1]]
        b=[rr]+[r*q for q in b[:-1]]
        new=sum(q*q for q in f+b)
        source+=a*a-br*br;load+=fr*fr-rr*rr;heat+=(1-r*r)*old
        assert new-old==a*a-br*br-(fr*fr-rr*rr)-(1-r*r)*old
    assert source==load+heat+sum(q*q for q in f+b)
    assert load>=0 and heat>=0
    return {'exact_rational_conservation':True,
            'reflection_count':'two passive boundaries plus interfering source drive',
            'energy_balance_residual':'0',
            'note':'All values Fraction; common positive energy factor suppressed'}


def smooth_delay_error_bound(samples,dt_s:float,cells:int,impedance_ohm:float):
    """Certified discrete-data Lipschitz bound for a matched delayed line.

    If the *inter-sample signal is piecewise linear*, K=max|Δu|/dt.
    |u(t)-u(t-tau)|<=K tau.  Power bound assumes |u|<=M everywhere.
    NOT valid for an unbounded instantaneous switching edge or unknown
    high-frequency between-sample content.
    """
    a=np.asarray(samples,dtype=float)
    if cells<1 or len(a)<=cells or dt_s<=0 or impedance_ohm<=0:
        raise ValueError('invalid delay / sample geometry')
    K=float(np.max(np.abs(np.diff(a)))/dt_s)
    M=float(np.max(np.abs(a)))
    flight=dt_s*cells
    error=np.abs(a[cells:]-a[:-cells])
    power_error=np.abs(a[cells:]**2-a[:-cells]**2)/(4*impedance_ohm)
    amp_bound=K*flight
    power_bound=(2*M*K*flight)/(4*impedance_ohm)
    assert float(np.max(error)) <= amp_bound+1e-9*max(1,amp_bound)
    assert float(np.max(power_error)) <= power_bound+1e-9*max(1,power_bound)
    return dict(flight_s=flight,lipschitz_v_per_s=K,amplitude_bound_v=amp_bound,
                amplitude_max_observed_v=float(max(error)),
                power_bound_w=power_bound,power_max_observed_w=float(max(power_error)),
                scope='matched passive delay, piecewise-linear input; excludes discontinuous and unobserved edges')


def causal_clock_scales(length_m=.5,factor_c=.7,switching_hz=20_000,
                        edge_s=2e-9,rotor_rpm=2354,harmonic=4):
    line=CausalLine(length_m=length_m,front_speed_m_s=factor_c*C0)
    tau=line.flight_s
    return {'flight_s':tau,'front_speed_m_s':line.front_speed_m_s,
            'carrier_phase_rad':2*math.pi*switching_hz*tau,
            'electrical_phase_rad':2*math.pi*(rotor_rpm/60)*harmonic*tau,
            'delay_over_switch_edge':tau/edge_s,
            'fundamental_small_phase_not_edge_certificate':True}


def run():
    tl=telegrapher_identity()
    rat=exact_fraction_certificate()
    line=CausalLine(amplitude_survival_per_tick=.98,load_reflection=.3,source_reflection=-.25)
    pulse=[1.5,0.,0.,-.4]+[0.]*88
    result=traveling_packets(line,pulse,7)
    assert result['first_forward_arrival_tick']==7
    assert abs(result['energy_residual_j'])<1e-21
    t=np.linspace(0,2e-6,501)
    s=4*np.sin(2*np.pi*1e6*t)
    lip=smooth_delay_error_bound(s,float(t[1]-t[0]),5,50.)
    return dict(scope='mathematical 1D passive causal transmission line, NOT same-device V2 measurement',
                continuum_identity=tl,exact_rational_finite_certificate=rat,
                reflected_lossy_line={k:v for k,v in result.items() if k!='trace'},
                quasistatic_lipschitz_certificate=lip,
                physical_clock_example=causal_clock_scales(),
                gates_open=['actual source material and Maxwell boundary',
                            'rigorous dispersive front and passivity',
                            'quasistatic bound for nonlinear multi-coil field including switching edges',
                            'original V2 topology and metrology'])

if __name__=='__main__':
    print(json.dumps(run(),indent=2))