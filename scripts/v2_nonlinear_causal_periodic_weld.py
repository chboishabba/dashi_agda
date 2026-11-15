#!/usr/bin/env python3
"""Constructive nonlinear, mutually coupled periodic reluctance machine.

A RESTRICTED exact analytical theorem, not V2 calibration or a continuum
Maxwell proof. Voltage/current signals are time smooth (ideal averaged bridge).
The causal port is a pure-delay, matched waveguide, not a magic synchronous
remote net: an unexpected change is observable only after the flight time.

At a given rotor angle, reversible co-energy W'(i,theta) is uniformly strongly
convex with Hessian eigs in [ell,Lambda]. Flux psi=grad_i W' and dynamics
psi_dot=v(t)-R*i(psi,theta). For equal periodic voltage v and rotor angle,
||psi1(T)-psi2(T)|| <= exp(-R*T/Lambda)*||psi1(0)-psi2(0)||.
Banach's fixed-point theorem yields a unique globally attracting periodic flux
solution, including mutual inductance and smooth nonlinear saturation.

This does NOT model magnetic memory/hysteresis or prove the same for the
previous relay/PWM nonlinear lag controller; those remain open.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import json
import math
import numpy as np
from scipy.integrate import solve_ivp

C0=299_792_458.0

@dataclass(frozen=True)
class Parameters:
    phases:int=3
    rpm:float=2354.0
    harmonic:int=4
    base_h:float=.040
    swing_h:float=.012
    mutual_h:float=.0012
    saturation_h:float=.004
    saturation_a:float=5.0
    r_ohm:float=1.0
    i0_a:float=1.0
    i1_a:float=.6
    bus_v:float=320.0
    cable_m:float=.5
    wavefront_speed_m_s:float=.7*C0

    @property
    def omega(self):return 2*math.pi*self.rpm/60
    @property
    def period(self):return 2*math.pi/self.omega
    @property
    def lower(self):return self.base_h-abs(self.swing_h)-2*abs(self.mutual_h)
    @property
    def upper(self):return self.base_h+abs(self.swing_h)+2*abs(self.mutual_h)+self.saturation_h
    @property
    def contraction(self):return math.exp(-self.r_ohm*self.period/self.upper)
    @property
    def delay_s(self):return self.cable_m/self.wavefront_speed_m_s

    def check(self):
        if (self.phases<3 or self.harmonic<1 or self.rpm<=0 or
            self.base_h<=abs(self.swing_h)+2*abs(self.mutual_h) or
            self.saturation_h<=0 or self.saturation_a<=0 or
            self.r_ohm<=0 or self.i0_a<abs(self.i1_a) or self.i1_a<=0 or
            self.bus_v<=0 or self.cable_m<=0 or
            not (0<self.wavefront_speed_m_s<=C0)):
            raise ValueError('non-passive, noncausal or ill-posed parameters')
        return self


def geometry(p:Parameters,t:float):
    m=p.phases
    angle=p.harmonic*p.omega*t-2*math.pi*np.arange(m)/m
    L=np.diag(p.base_h+p.swing_h*np.cos(angle))
    for j in range(m):
        k=(j+1)%m
        L[j,k]+=p.mutual_h
        L[k,j]+=p.mutual_h
    # Time derivatives, including rotor motion (no instantaneous propagation
    # claim: this is the quasistatic constitutive model only).
    Ldot=np.diag(-p.swing_h*p.harmonic*p.omega*np.sin(angle))
    return L,Ldot,angle


def target(p:Parameters,t:float):
    phase=p.harmonic*p.omega*t-2*math.pi*np.arange(p.phases)/p.phases
    sq=math.sqrt(p.phases)
    i=(p.i0_a+p.i1_a*np.sin(phase))/sq
    di=p.i1_a*p.harmonic*p.omega*np.cos(phase)/sq
    ddi=-p.i1_a*(p.harmonic*p.omega)**2*np.sin(phase)/sq
    return i,di,ddi


def constitutive(p:Parameters,t:float,i:np.ndarray):
    L,Ldot,_=geometry(p,t)
    arg=i/p.saturation_a
    sech2=1/np.cosh(arg)**2
    psi=L@i+p.saturation_h*p.saturation_a*np.tanh(arg)
    H=L+np.diag(p.saturation_h*sech2)
    co=.5*float(i@L@i)+p.saturation_h*p.saturation_a**2*float(np.sum(np.logaddexp(arg,-arg)-math.log(2)))
    U=float(i@psi-co)
    torque=.5*float(i@Ldot@i)/p.omega
    return psi,H,U,torque,Ldot


def commanded_voltage(p:Parameters,t:float):
    i,di,_=target(p,t)
    _,H,_,_,Ldot=constitutive(p,t,i)
    return p.r_ohm*i+H@di+Ldot@i


def analytic_bounds(p:Parameters):
    p.check();m=p.phases;w=p.omega;h=p.harmonic
    i_max=(p.i0_a+abs(p.i1_a))/math.sqrt(m)
    d_max=abs(p.i1_a)*h*w/math.sqrt(m)
    dd_max=abs(p.i1_a)*(h*w)**2/math.sqrt(m)
    upper=p.upper
    v_max=p.r_ohm*i_max+upper*d_max+abs(p.swing_h)*h*w*i_max
    # Differentiating v=Ri+H(i,theta)i_dot + Ldot(theta)i.
    # Hdot*i_dot includes (Ldot)i_dot and the saturation derivative term.
    vdot_max=(p.r_ohm*d_max+upper*dd_max+
              2*abs(p.swing_h)*h*w*d_max+
              abs(p.swing_h)*(h*w)**2*i_max+
              (2*p.saturation_h/p.saturation_a)*d_max*d_max)
    k=p.r_ohm/upper
    delay=p.delay_s
    # Entire nonlinear flux-state ODE: delayed, otherwise equal voltage
    # forcing changes the flux by <= (dv/k)*(1-exp(-kt)).
    delta_drive_2=math.sqrt(m)*vdot_max*delay
    flux_error_ultimate=delta_drive_2/k
    current_error_ultimate=flux_error_ultimate/p.lower
    return dict(min_incremental_inductance_h=p.lower,
                max_incremental_inductance_h=upper,
                contraction_rate_per_s=k,
                cycle_contraction=p.contraction,
                current_component_envelope_a=i_max,
                current_slew_component_envelope_a_per_s=d_max,
                commanded_voltage_component_bound_v=v_max,
                command_lipschitz_component_bound_v_per_s=vdot_max,
                bus_voltage_feasible=bool(v_max<=p.bus_v),
                physical_delay_s=delay,
                delay_lower_bound_s=p.cable_m/C0,
                delayed_drive_difference_2norm_bound_v=delta_drive_2,
                nonlinear_flux_error_ultimate_2norm_wb=flux_error_ultimate,
                nonlinear_current_error_ultimate_2norm_a=current_error_ultimate)


def solve_perturbation(p:Parameters,cycles:int=1,initial_current_delta:float=.2,delay:float=0.0):
    """Independent numerical witness to the rigorous flux contraction bounds.

    The analytic theorem bounds differences at a common rotor position;
    integration is a diagnostic and does NOT serve as the proof.
    """
    p.check()
    if cycles<1 or initial_current_delta<0 or delay<0:raise ValueError('invalid experiment')
    t0=0.0
    i0,_,_=target(p,0.)
    psi0,*_=constitutive(p,0.,i0)
    disturbed=i0+initial_current_delta*np.cos(np.arange(p.phases))
    psi_dist,*_=constitutive(p,0.,disturbed)
    def f(t,i):
        _,H,_,_,Ldot=constitutive(p,t,i)
        v=commanded_voltage(p,t-delay) if delay else commanded_voltage(p,t)
        return np.linalg.solve(H,v-p.r_ohm*i-Ldot@i)
    final_t=cycles*p.period
    s=solve_ivp(f,(0.,final_t),disturbed,rtol=2e-9,atol=5e-12,max_step=p.period/150)
    if not s.success:raise RuntimeError(s.message)
    ifin=s.y[:,-1]
    target_end,_,_=target(p,final_t)
    psi_end,*_=constitutive(p,final_t,ifin)
    psi_ref_end,*_=constitutive(p,final_t,target_end)
    err0=float(np.linalg.norm(psi_dist-psi0))
    err_final=float(np.linalg.norm(psi_end-psi_ref_end))
    rigorous_bound=err0*math.exp(-p.r_ohm/p.upper*final_t)
    if delay:
        B=analytic_bounds(p)
        rigorous_bound+=B['delayed_drive_difference_2norm_bound_v']/B['contraction_rate_per_s']*(1-math.exp(-B['contraction_rate_per_s']*final_t))
    return dict(phases=p.phases,cycles=cycles,delay_s=delay,
                initial_flux_error_norm_wb=err0,final_flux_error_norm_wb=err_final,
                analytic_error_upper_wb=rigorous_bound,
                contraction_verified=bool(err_final<=rigorous_bound+1e-10),
                terminal_current_error_a=float(np.linalg.norm(ifin-target_end)))


def energy_cycle(p:Parameters,samples:int=4096):
    p.check()
    if samples<16*p.phases:raise ValueError('too few sample points')
    t=np.arange(samples)*p.period/samples
    pts=[]
    for x in t:
        i,di,_=target(p,x)
        psi,H,U,tau,Ldot=constitutive(p,x,i)
        v=commanded_voltage(p,x)
        dU=float(i@(H@di+Ldot@i)-tau*p.omega)
        pts.append((float(v@i),p.r_ohm*float(i@i),tau*p.omega,dU,U,float(np.max(np.abs(v)))))
    pts=np.array(pts)
    res=pts[:,0]-pts[:,1]-pts[:,2]-pts[:,3]
    extracted=.5*p.swing_h*p.harmonic*p.omega*p.i0_a*p.i1_a
    copper=p.r_ohm*(p.i0_a**2+.5*p.i1_a**2)
    bound=analytic_bounds(p)
    return dict(phases=p.phases,nonlinear_and_mutually_coupled=True,
                exact_cycle_storage_closure='target i and constitutive theta are strictly periodic',
                shaft_extraction_w=extracted,copper_w=copper,
                ideal_bus_export_w=extracted-copper,
                analytic_voltage_upper_v=bound['commanded_voltage_component_bound_v'],
                measured_peak_voltage_v=float(max(pts[:,5])),
                average_energy_derivative_w=float(np.mean(pts[:,3])),
                pointwise_energy_residual_max_w=float(np.max(np.abs(res))),
                average_terminal_input_w=float(np.mean(pts[:,0])),
                mean_energy_storage_j=float(np.mean(pts[:,4])),
                cycle_contraction=p.contraction)


def delayed_source_precompensation(p:Parameters,t:float):
    """A programmed waveform can be launched tau early; no predictive sensor.

    Only for known periodic waveform + matched ideal pure-delay line. Unplanned
    disturbances remain strictly delayed; no future measurement is accessed.
    """
    tau=p.delay_s
    return dict(at_load_time=t,source_launch_time=t-tau,
                transmitted_voltage=commanded_voltage(p,t),
                source_wave_at_launch=commanded_voltage(p,(t-tau)+tau),
                assumption='preprogrammed periodic waveform; matched lossless line; no clairvoyant feedback')


def switching_edge_negative_control(p:Parameters,step_v:float=100.0):
    p.check()
    tau=p.delay_s
    a=lambda t: float(step_v if t>=0 else 0.)
    sample=tau/2
    return dict(delay_s=tau,local_step_at_time_t= a(sample),
                remotely_received_step_at_t=a(sample-tau),
                instantaneous_difference_v=abs(a(sample)-a(sample-tau)),
                violation_of_smooth_lipschitz_assumption=True)



def delayed_feedback_small_gain(p:Parameters, feedback_gain_ohm:float=.25,
                                controller_latency_s:float=.0001):
    """Conditional Halanay bound for a delayed *active* voltage feedback port.

    Flux dynamics: psi_dot = vbase(t)-R*i(t)+K*i(t-tau).
    Incremental inequality: D+e <= -a e(t)+b e(t-tau)
    with a=R/Lambda and b=|K|/ell. If b<a, exponential contraction
    is certified for nonnegative delays and the unique positive root eta
    of eta+b*exp(eta*tau)=a. A T-periodic solution exists uniquely by
    contraction of the periodic-input->periodic-response operator (b/a<1).

    K*i_delayed is an *externally supplied* source term; its signed work is
    always accounted for. This does not represent a passive Maxwell link.
    """
    from scipy.optimize import brentq
    p.check()
    if (not math.isfinite(feedback_gain_ohm) or
        not math.isfinite(controller_latency_s) or controller_latency_s<0):
        raise ValueError('invalid delayed feedback gain or latency')
    a=p.r_ohm/p.upper
    b=abs(feedback_gain_ohm)/p.lower
    delay=p.delay_s+controller_latency_s
    accepted=b<a
    if b==0:
        eta=a
    elif accepted:
        eta=float(brentq(lambda x:x+b*math.exp(x*delay)-a,0,a))
    else:
        eta=None
    return dict(phases=p.phases,feedback_gain_ohm=feedback_gain_ohm,
                frontend_cable_delay_s=p.delay_s,controller_latency_s=controller_latency_s,
                total_retarded_delay_s=delay,
                a_self_dissipation_per_s=a,b_delayed_gain_per_s=b,
                small_gain_margin_per_s=a-b,
                stable_periodic_orbit_certified=bool(accepted),
                exponential_history_convergence_per_s=eta,
                periodic_response_contraction=b/a,
                auxiliary_port_status='signed external feedback voltage K*i_delayed, not free energy')


def delayed_feedback_periodic_energy(p:Parameters,gain_ohm:float=.25,
                                     latency_s:float=.0001,samples:int=2048):
    """Constructive periodic orbit with genuinely delayed active feedback.

    The base source is a known precomputed periodic waveform. Controller
    voltage responds only to i(t-tau); total terminal voltage is v_star(t).
    Signed feedback work is an EXTERNAL source, never extra energy.
    """
    gate=delayed_feedback_small_gain(p,gain_ohm,latency_s)
    if not gate['stable_periodic_orbit_certified']:
        raise ValueError('small gain insufficient to certify this controller')
    tau=gate['total_retarded_delay_s']
    arr=[]
    for t in np.arange(samples)*p.period/samples:
        now,_,_=target(p,float(t));previous,_,_=target(p,float(t-tau))
        feedback=gain_ohm*previous
        full=commanded_voltage(p,float(t))
        base=full-feedback
        arr.append((float(base@now),float(feedback@now),float(full@now),
                    float((base+feedback-full)@now)))
    a=np.asarray(arr)
    return dict(phases=p.phases,delay_s=tau,
                base_drive_work_mean_w=float(np.mean(a[:,0])),
                external_feedback_work_mean_w=float(np.mean(a[:,1])),
                total_terminal_work_mean_w=float(np.mean(a[:,2])),
                maximum_pointwise_port_balance_error_w=float(np.max(np.abs(a[:,3]))),
                intended_periodic_waveform_is_exact_solution=True,
                small_gain=gate,
                limitation='Controller active-port signed work fully counted; actual feedback hardware not identified')

def run():
    rows=[]
    for m in (3,4,5,6,7,8,9,10,11,12):
        p=Parameters(phases=m)
        b=analytic_bounds(p)
        e=energy_cycle(p,samples=max(1024,64*m))
        rows.append(dict(phases=m,bounds=b,energy=e))
    return dict(scope='nonlinear reversible saturating + mutual quasi-static motor, NOT actual V2 or Maxwell continuum',
                assumptions=asdict(Parameters()),
                mathematical_theorem='flux-state global one-cycle contraction and unique periodic orbit for any periodic voltage and rotor angle; positive R, Hessian in [ell,Lambda]',
                source_attribution='DASHI conditional model; finite light-cone from distinct Don Smith donor, no hardware equivalence',
                phase_rows=rows,
                attractor_check=solve_perturbation(Parameters(),cycles=2),
                delayed_check=solve_perturbation(Parameters(),cycles=2,delay=Parameters().delay_s),
                edge_control=switching_edge_negative_control(Parameters()),
                retarded_feedback_small_gain=delayed_feedback_small_gain(Parameters()),
                retarded_feedback_port_ledger=delayed_feedback_periodic_energy(Parameters()),
                open_gates=['actual waveguide/Maxwell field-to-machine weld',
                            'hysteretic lag controller nonlinear periodic orbit',
                            'Agda real calculus and kernel verification',
                            'actual V2 netlist, geometry, losses, sources, timing, sensors'])

if __name__=='__main__':print(json.dumps(run(),indent=2))
