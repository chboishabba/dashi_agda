#!/usr/bin/env python3
"""A genuinely retarded, passive-memory nonlinear reluctance periodic theorem.

THEOREM (restricted model): Let F_theta(i)=L(theta)i+b*Is*tanh(i/Is),
 ell I <= dF/di <= Lambda I, and psi=F_theta(i)+g z. Assume R>0,
 z'=mu(g i-h z), mu>0, h>g²/ell. For periodic theta and vbase and
 terminal voltage v=vbase+K i(t-tau), with tau>=d/c (also includes optional
 controller latency), two solutions have flux/memory difference norms x,y:
 D+x <= -(R/Lambda)x+(R*g/ell)y+(|K|/ell)(x_tau+g*y_tau)
 D+y <= (mu*g/ell)x-mu(h-g²/ell)y.
 For rho>0, M=max(x,rho*y), a=min(R/Lambda-R*g/(ell*rho),
 mu*(h-g²/ell)-rho*mu*g/ell), b=|K|/ell*(1+g/rho).
 If a>b>=0, M(t)<= M_history exp(-eta*t) for the positive root
 eta+b exp(eta*tau)=a (Halanay); period map on histories contracts
 after sufficiently many periods, yielding unique attracting periodic state.
 All port work is explicit: v.i=Ri²+dU/dt+omega*tau_e+mu||gi-hz||²,
 U=i.psi-W'(i,theta,z). No isolated V2 hardware or full Maxwell theorem.

A manufactured periodic i*(t) and z*(t) give one explicit periodic orbit
with finite continuous voltage, including saturation, mutual coupling and
lossy memory. Delayed feedback is EXTERNAL active controller work.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
import json
import math
import numpy as np
from scipy.optimize import brentq
from scipy.integrate import solve_ivp

C0=299_792_458.


@dataclass(frozen=True)
class MemoryMachine:
    phases:int=3
    rpm:float=2354.
    harmonic:int=4
    base_h:float=.040
    swing_h:float=.012
    mutual_h:float=.0012
    saturating_h:float=.004
    saturation_a:float=5.
    resistance_ohm:float=1.
    coupling_g:float=.003
    memory_h:float=.003
    mobility:float=12000.
    current_dc_a:float=1.
    current_ac_a:float=.6
    voltage_limit_v:float=320.
    cable_m:float=.5
    front_m_s:float=.7*C0
    processing_latency_s:float=0.0001
    feedback_gain_ohm:float=.04

    @property
    def omega(self):return 2*math.pi*self.rpm/60
    @property
    def cycle_s(self):return 2*math.pi/self.omega
    @property
    def harmonics_per_s(self):return self.omega*self.harmonic
    @property
    def ell(self):return self.base_h-abs(self.swing_h)-2*abs(self.mutual_h)
    @property
    def Lambda(self):return self.base_h+abs(self.swing_h)+2*abs(self.mutual_h)+self.saturating_h
    @property
    def light_delay_s(self):return self.cable_m/self.front_m_s
    @property
    def total_delay_s(self):return self.light_delay_s+self.processing_latency_s

    def check(self):
        if (self.phases<3 or self.harmonic<1 or self.rpm<=0 or self.ell<=0 or
            self.Lambda<=self.ell or self.saturation_a<=0 or self.saturating_h<0 or
            self.resistance_ohm<=0 or self.coupling_g<0 or self.memory_h<=0 or
            self.mobility<=0 or self.memory_h<=self.coupling_g**2/self.ell or
            self.current_dc_a<abs(self.current_ac_a) or self.current_ac_a<=0 or
            self.voltage_limit_v<=0 or self.cable_m<=0 or
            not(0<self.front_m_s<=C0) or self.processing_latency_s<0 or
            not math.isfinite(self.feedback_gain_ohm)):
            raise ValueError('unsafe nonlinear, delayed, or constitutive parameters')
        return self


def geometry(p:MemoryMachine,t:float):
    angles=p.harmonics_per_s*t-2*math.pi*np.arange(p.phases)/p.phases
    L=np.diag(p.base_h+p.swing_h*np.cos(angles))
    for j in range(p.phases):
        k=(j+1)%p.phases
        L[j,k]+=p.mutual_h
        L[k,j]+=p.mutual_h
    Ldot=np.diag(-p.swing_h*p.harmonics_per_s*np.sin(angles))
    return L,Ldot,angles


def reference(p:MemoryMachine,t:float):
    phase=p.harmonics_per_s*t-2*math.pi*np.arange(p.phases)/p.phases
    root=math.sqrt(p.phases)
    i=(p.current_dc_a+p.current_ac_a*np.sin(phase))/root
    di=p.current_ac_a*p.harmonics_per_s*np.cos(phase)/root
    # The exact, periodic, causal response of z'=mu(g*i-h*z):
    gamma=p.mobility*p.memory_h
    lag=math.atan2(p.harmonics_per_s,gamma)
    za=p.mobility*p.coupling_g*p.current_ac_a/root / math.hypot(gamma,p.harmonics_per_s)
    z=(p.coupling_g/p.memory_h)*p.current_dc_a/root+za*np.sin(phase-lag)
    dz=p.mobility*(p.coupling_g*i-p.memory_h*z)
    return i,di,z,dz


def constitutive(p:MemoryMachine,t:float,i:np.ndarray,z:np.ndarray):
    L,Ldot,_=geometry(p,t)
    r=i/p.saturation_a
    sech2=1/np.cosh(r)**2
    H=L+np.diag(p.saturating_h*sech2)
    flux=L@i+p.saturating_h*p.saturation_a*np.tanh(r)+p.coupling_g*z
    coenergy=(.5*float(i@L@i)+p.saturating_h*p.saturation_a**2*
              float(np.sum(np.logaddexp(r,-r)-math.log(2)))+
              p.coupling_g*float(i@z)-.5*p.memory_h*float(z@z))
    energy=float(i@flux)-coenergy
    torque_w=.5*float(i@Ldot@i)
    memory_force=p.coupling_g*i-p.memory_h*z
    return flux,H,energy,torque_w,memory_force,Ldot


def inverse_flux(p:MemoryMachine,t:float,flux:np.ndarray,z:np.ndarray,guess:np.ndarray):
    """Monotone SPD constitutive inverse, numerically via damped Newton."""
    L,_,_=geometry(p,t)
    rhs=flux-p.coupling_g*z
    i=guess.copy()
    for _ in range(16):
        r=i/p.saturation_a
        f=L@i+p.saturating_h*p.saturation_a*np.tanh(r)-rhs
        if np.max(np.abs(f))<2e-13:break
        H=L+np.diag(p.saturating_h/np.cosh(r)**2)
        i-=np.linalg.solve(H,f)
    if np.max(np.abs(L@i+p.saturating_h*p.saturation_a*np.tanh(i/p.saturation_a)-rhs))>1e-9:
        raise RuntimeError('nonlinear constitutive inverse failed')
    return i


def manufactured_voltage(p:MemoryMachine,t:float):
    i,di,z,dz=reference(p,t)
    flux,H,_,_,_,Ldot=constitutive(p,t,i,z)
    return p.resistance_ohm*i + H@di + Ldot@i + p.coupling_g*dz


def voltage_bound(p:MemoryMachine):
    p.check()
    m=p.phases; a=(p.current_dc_a+abs(p.current_ac_a))/math.sqrt(m)
    d=abs(p.current_ac_a)*p.harmonics_per_s/math.sqrt(m)
    # z*(t) is a stable lowpass of i*(t), so |z|<=g*a/h.
    # |z'|<=mu*(g*a+h*g*a/h)=2mu*g*a (conservative).
    bound=p.resistance_ohm*a+p.Lambda*d+abs(p.swing_h)*p.harmonics_per_s*a+2*p.mobility*p.coupling_g**2*a
    feedback=abs(p.feedback_gain_ohm)*a
    return dict(terminal_voltage_component_v=bound,
                base_source_voltage_component_v=bound+feedback,
                delayed_feedback_component_v=feedback,
                current_component_a=a,current_slew_component_a_per_s=d,
                continuous_voltage_feasible=bool(bound<=p.voltage_limit_v),
                delayed_controller_base_voltage_feasible=bool(bound+feedback<=p.voltage_limit_v))


def memory_small_gain(p:MemoryMachine):
    p.check()
    r=p.resistance_ohm; g=p.coupling_g; e=p.ell; L=p.Lambda; mu=p.mobility; h=p.memory_h
    a=r/L; b=r*g/e; c=mu*g/e; d=mu*(h-g*g/e)
    # Choose the positive weight where both current and memory margins match.
    rho=(2*b/(math.sqrt((a-d)**2+4*c*b)+(a-d))) if c>0 and math.sqrt((a-d)**2+4*c*b)+(a-d)>1e-14 else ((d-a+math.sqrt((a-d)**2+4*c*b))/(2*c) if c>0 else 1.)
    # Root of c*rho²+(a-d)*rho-b=0: balances the two dissipative margins.
    margin=min(a-b/rho,d-rho*c)
    delayed=abs(p.feedback_gain_ohm)/e*(1+g/rho)
    certified=margin>delayed and margin>0
    if delayed==0 and margin>0:eta=margin
    elif certified:eta=float(brentq(lambda x:x+delayed*math.exp(x*p.total_delay_s)-margin,0,margin))
    else:eta=None
    return dict(weight_rho=rho,flux_damping_a=a,memory_cross_b=b,
                flux_cross_c=c,memory_damping_d=d,
                instantaneous_margin_per_s=margin,delayed_gain_per_s=delayed,
                certified=bool(certified),history_decay_rate_per_s=eta,
                retarded_delay_s=p.total_delay_s,cable_light_front_s=p.light_delay_s,
                sufficient_condition='min(R/Lambda-R*g/(ell*rho),mu*(h-g²/ell)-rho*mu*g/ell)>abs(K)/ell*(1+g/rho)',
                scope='passive single-rate relaxing memory; not general Preisach hysteresis or Maxwell wave solution')


def periodic_ledger(p:MemoryMachine,samples:int=2048):
    p.check()
    if samples<32*p.phases:raise ValueError('insufficient phase resolution')
    times=np.arange(samples)*p.cycle_s/samples
    rows=[]
    for t in times:
        i,di,z,dz=reference(p,float(t)); iold,_,_,_=reference(p,float(t-p.total_delay_s))
        psi,H,U,torque,force,Ldot=constitutive(p,float(t),i,z)
        terminal=manufactured_voltage(p,float(t))
        feedback=p.feedback_gain_ohm*iold
        base=terminal-feedback
        fluxdot=H@di+Ldot@i+p.coupling_g*dz
        # Independent derivative of U via explicit Legendre-form expression.
        dU=float(i@(H@di) +.5*i@Ldot@i+p.memory_h*z@dz)
        heat=p.mobility*float(force@force)
        copper=p.resistance_ohm*float(i@i)
        identity=float(i@terminal)-copper-dU-torque-heat
        rows.append((float(i@terminal),float(i@base),float(i@feedback),
                     copper,dU,torque,heat,U,identity,float(np.max(np.abs(terminal))),
                     float(np.max(np.abs(base)))))
    a=np.asarray(rows)
    energy0=constitutive(p,0.,*reference(p,0.)[::2])[2] # [i,z] indexed by 0,2
    energyT=constitutive(p,p.cycle_s,*reference(p,p.cycle_s)[::2])[2]
    res=voltage_bound(p)
    return dict(phase_count=p.phases,certified_small_gain=memory_small_gain(p),
                exact_periodic_reference=True,exact_storage_endpoint_identity='i*(t+T)=i*(t), z*(t+T)=z*(t), theta(t+T)=theta(t)',
                endpoint_storage_difference_j=float(energyT-energy0),
                source_base_power_w=float(np.mean(a[:,1])),
                delayed_active_controller_work_w=float(np.mean(a[:,2])),
                terminal_power_w=float(np.mean(a[:,0])),
                generator_shaft_extraction_w=float(-np.mean(a[:,5])),
                copper_loss_w=float(np.mean(a[:,3])),
                memory_dissipation_w=float(np.mean(a[:,6])),
                cyclic_energy_derivative_w=float(np.mean(a[:,4])),
                exported_terminal_power_w=float(-np.mean(a[:,0])),
                power_balance_max_abs_w=float(np.max(np.abs(a[:,8]))),
                observed_voltage_max_v=float(np.max(a[:,9])),
                observed_base_max_v=float(np.max(a[:,10])),
                voltage_analytic=res,
                assumptions='constructed smooth averaged controller with independent active delayed K port; not source hardware')


def run(phases=(3,4,5,6,7,8,9,10,11,12)):
    rows=[periodic_ledger(MemoryMachine(phases=m),samples=1024) for m in phases]
    return dict(theorem='weighted flux+memory retarded Halanay contraction, periodic forced solution, and passivity identity',
                scope='constructed nonlinear mutually coupled saturating machine with passive relaxing magnetic memory and delayed active controller; not original V2',
                parameters=asdict(MemoryMachine()),cases=rows,
                max_pointwise_residual_w=max(r['power_balance_max_abs_w'] for r in rows),
                every_model_certified=all(r['certified_small_gain']['certified'] for r in rows),
                all_continuous_bus_bounds_pass=all(r['voltage_analytic']['continuous_voltage_feasible'] for r in rows),
                original_hardware_gates='OPEN: V2 original netlist/geometry/losses/shaft/power/probe and Agda kernel')




def integrate_delayed_history(p:MemoryMachine, cycles:int=2,
                              initial_i_perturb_a:float=.1,
                              initial_z_perturb_a:float=.01,
                              steps_per_delay:int=8):
    """Numerical method-of-steps witness; NOT the analytic stability proof.

    Stores previous current states; the remote feedback reads ONLY t-tau,
    and the integration step is shorter than the total causal+controller delay.
    The source base(t) is a preprogrammed known periodic waveform.
    """
    gate=memory_small_gain(p)
    if not gate['certified']:
        raise ValueError('cannot claim history contraction without sufficient margin')
    if not (cycles>=1 and initial_i_perturb_a>=0 and
            initial_z_perturb_a>=0 and steps_per_delay>=3):
        raise ValueError('invalid numerical delay experiment')
    tau=p.total_delay_s
    steps=int(math.ceil(cycles*p.cycle_s/(tau/steps_per_delay)))
    dt=cycles*p.cycle_s/steps
    assert dt<tau
    ii,_,zz,_=reference(p,0.)
    di=initial_i_perturb_a*np.cos(np.arange(p.phases))
    dz=initial_z_perturb_a*np.sin(np.arange(p.phases)+.5)
    istart=ii+di; zstart=zz+dz
    psistart,*_=constitutive(p,0.,istart,zstart)
    y=np.r_[psistart,zstart]
    times=[0.]
    currents=[istart]

    def delayed_current(s):
        lagged=s-tau
        if lagged<0.:
            return reference(p,lagged)[0]+di
        at=lagged/dt
        left=int(math.floor(at))
        if left+1>=len(currents):
            return currents[-1]
        blend=at-left
        return currents[left]*(1-blend)+currents[left+1]*blend

    def rhs(s,state):
        psi=state[:p.phases];z=state[p.phases:]
        i=inverse_flux(p,s,psi,z,reference(p,s)[0])
        iminus=delayed_current(s)
        vbase=manufactured_voltage(p,s)-p.feedback_gain_ohm*reference(p,s-tau)[0]
        return np.r_[vbase+p.feedback_gain_ohm*iminus-p.resistance_ohm*i,
                     p.mobility*(p.coupling_g*i-p.memory_h*z)]

    eps0=max(p.Lambda*np.linalg.norm(di)+p.coupling_g*np.linalg.norm(dz),
             gate['weight_rho']*np.linalg.norm(dz))
    worst_over=0.
    for n in range(steps):
        t=n*dt
        k1=rhs(t,y)
        k2=rhs(t+dt/2,y+dt*k1/2)
        k3=rhs(t+dt/2,y+dt*k2/2)
        k4=rhs(t+dt,y+dt*k3)
        y=y+dt*(k1+2*k2+2*k3+k4)/6
        end=t+dt
        i=inverse_flux(p,end,y[:p.phases],y[p.phases:],reference(p,end)[0])
        times.append(end);currents.append(i)
        iref,_,zref,_=reference(p,end)
        psiref,*_=constitutive(p,end,iref,zref)
        M=max(float(np.linalg.norm(y[:p.phases]-psiref)),
              gate['weight_rho']*float(np.linalg.norm(y[p.phases:]-zref)))
        worst_over=max(worst_over,M-eps0*math.exp(-gate['history_decay_rate_per_s']*end))
    iref,_,zref,_=reference(p,cycles*p.cycle_s)
    end_flux,*_=constitutive(p,cycles*p.cycle_s,iref,zref)
    actual=max(float(np.linalg.norm(y[:p.phases]-end_flux)),
               gate['weight_rho']*float(np.linalg.norm(y[p.phases:]-zref)))
    return dict(phase_count=p.phases,cycles=cycles,
                interpolation='causal method of steps RK4, historical current only; NOT rigorous ODE enclosure',
                step_s=dt,total_delay_s=tau,step_is_shorter_than_delay=bool(dt<tau),
                history_envelope_bound=eps0,analytic_final_bound=eps0*math.exp(-gate['history_decay_rate_per_s']*cycles*p.cycle_s),
                observed_final_weighted_error=actual,
                worst_numeric_bound_exceedance=worst_over,
                pointwise_bounds_numerically_satisfied=bool(worst_over<=1e-5))


def exact_two_winding_memory_identity():
    """Exact SymPy proof, independent differentiation of W' and its Legendre U.

    Includes angle dependent self-inductance, constant mutual flux,
    saturating tanh, and separate passive magnetic-memory coordinates.
    """
    import sympy as s
    th, w, Is, L0, A, M, B, g, h, mu=s.symbols('th w Is L0 A M B g h mu',real=True)
    i1,i2,z1,z2=s.symbols('i1 i2 z1 z2',real=True)
    d1,d2=s.symbols('d1 d2',real=True)
    inds=(i1,i2);states=(z1,z2)
    L1=L0+A*s.cos(th);L2=L0+A*s.sin(th)
    co=((L1*i1*i1+2*M*i1*i2+L2*i2*i2)/2+
        B*Is**2*(s.log(s.cosh(i1/Is))+s.log(s.cosh(i2/Is)))+
        g*(i1*z1+i2*z2)-h*(z1*z1+z2*z2)/2)
    psi=[s.diff(co,x) for x in inds]
    fz=[s.diff(co,x) for x in states]
    U=sum(x*f for x,f in zip(inds,psi))-co
    zd=[mu*x for x in fz]
    rates=dict(zip((i1,i2,z1,z2,th),(d1,d2,zd[0],zd[1],w)))
    def total(f):return sum(s.diff(f,k)*v for k,v in rates.items())
    residual=sum(x*total(f) for x,f in zip(inds,psi))-total(U)-s.diff(co,th)*w-sum(a*b for a,b in zip(fz,zd))
    result=s.simplify(s.expand(residual))
    if result!=0:raise AssertionError(f'coenergy identity failed: {result}')
    return dict(exact_identity='sum_i i*d(lambda_i)/dt = dU/dt + tau*omega + mu*sum_j(dWco/dz_j)^2',
                sympy_residual='0',two_windings=True,
                full_material_scope='reversible saturating coenergy with passive single-rate magnetic memory')




def conditional_telegrapher_machine_port_weld():
    """Composition of SAME signed end-port, not a solved Maxwell coupling.

    From telegrapher on finite spatial path:
      dEline/dt=Psource-Pmotor-Plineheat
    and motor coenergy with passive lag:
      dUm/dt=Pmotor+Pshaft_input-Pcu-Pmemory.
    If and ONLY IF line load boundary and coil terminals are physically the
    *same* signed port, their equal-and-opposite internal Pmotor cancels.
    This proves a mathematical conservation law without assigning instantaneous
    remote influence or claiming a coupled retarded Maxwell PDE solution.
    """
    import sympy as s
    from fractions import Fraction
    source,shaft,port,line_heat,copper,memory=s.symbols('source shaft port line_heat copper memory',real=True)
    dEline=source-port-line_heat
    dEmotor=port+shaft-copper-memory
    residual=s.expand(dEline+dEmotor-source-shaft+line_heat+copper+memory)
    if residual!=0:raise AssertionError('compositional line/motor balance failed')
    # Negative signed motor port: machine injects into line, not an impossible
    # "negative passive load" absorbed by the earlier resistor-only packet model.
    WS=Fraction(2); WM=Fraction(6); loss=Fraction(1)
    dLine=Fraction(3);cu=Fraction(1);mem=Fraction(1,2)
    P=WS-loss-dLine
    dMachine=P+WM-cu-mem
    assert P<0
    assert dLine+dMachine==WS+WM-loss-cu-mem
    return dict(exact_symbolic_residual='0',signed_motor_port_j=str(P),
                exact_fraction_composed_residual='0',
                motor_negative_port_is_active='yes; prior passive-resistor packet model alone does not implement this boundary',
                conditional_assumption='same signed, causal physical boundary VI at line endpoint and motor winding terminals',
                strict_unclosed='actual bidirectional wave/motor Maxwell boundary existence, constitutive geometry, original physical ports')

if __name__=='__main__':
    report=run()
    report['sympy_exact_two_winding']=exact_two_winding_memory_identity()
    report['independent_history_witnesses']=[integrate_delayed_history(MemoryMachine(phases=m),cycles=2,steps_per_delay=5) for m in (3,6)]
    report['conditional_port_composition']=conditional_telegrapher_machine_port_weld()
    print(json.dumps(report,indent=2))
