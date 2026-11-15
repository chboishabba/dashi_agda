#!/usr/bin/env python3
"""Dynamic finite-flight, bidirectional waveguide <-> nonlinear reluctance motor.

A finite packet queue is coupled to an independently solved magnetic/memory
load at the SAME signed voltage-current port (not merely algebraic matching).
The motor uses a discrete-gradient energy step, so line+motor conservation is
an acceptance result for a CONSTRUCTED finite-dimensional model. Rotation is
advanced by a separately metered fixed-flux mechanical work split.

Not a continuum Maxwell solution, exact semiconductor PWM, validated numeric
flow, rate-independent hysteresis, or the hardware of @madscience369 V2.
The line cells correspond to a real distance v_front*dt: choosing a slow
motor timestep makes a physically LONG illustrative cable. Never insert an
entire motor-solver timestep as the delay of a short original cable.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict
from fractions import Fraction
from math import pi
import json
import numpy as np
from scipy.optimize import root

C0=299_792_458.0

@dataclass(frozen=True)
class Params:
    phases:int=3
    dt_s:float=2.0e-5
    delay_cells:int=3
    front_m_s:float=0.7*C0
    characteristic_ohm:float=6.
    line_transmission:float=0.985  # per-cell field amplitude; <=1 passive
    resistance_ohm:float=1.
    l0_h:float=0.04
    lharm_h:float=0.008
    mutual_h:float=0.0006
    saturation_h:float=0.003
    saturation_a:float=3.
    coupling_g:float=0.002
    memory_h:float=0.004
    memory_mobility:float=5500.
    omega_rad_s:float=2*pi*2354/60
    pole_harmonic:int=4
    def check(self):
        if self.phases<2 or self.delay_cells<1 or self.pole_harmonic<1:raise ValueError('positive phase/flight geometry required')
        scalar=(self.dt_s,self.front_m_s,self.characteristic_ohm,self.resistance_ohm,
                self.l0_h,self.saturation_a,self.memory_h,self.memory_mobility)
        if not all(np.isfinite(x) and x>0 for x in scalar):raise ValueError('positive finite model parameters required')
        nonneg=(self.saturation_h,self.mutual_h,self.coupling_g,self.lharm_h,self.omega_rad_s)
        if not all(np.isfinite(x) and x>=0 for x in nonneg):raise ValueError('nonnegative finite material/rotation parameters required')
        if self.front_m_s>C0:raise ValueError('wavefront exceeds c')
        if not np.isfinite(self.line_transmission) or not 0<=self.line_transmission<=1:raise ValueError('passive line amplitude required')
        if self.l0_h <= abs(self.lharm_h)+2*abs(self.mutual_h):raise ValueError('incremental inductance must be SPD')
        return self
    @property
    def delay_s(self):return self.dt_s*self.delay_cells
    @property
    def cable_m(self):return self.front_m_s*self.delay_s


def matrices(p:Params,theta:float):
    phases= p.phases
    angles=p.pole_harmonic*theta-2*pi*np.arange(phases)/phases
    L=np.diag(p.l0_h+p.lharm_h*np.cos(angles))
    for j in range(phases):
        k=(j+1)%phases
        L[j,k]+=p.mutual_h
        L[k,j]+=p.mutual_h
    dL=np.diag(-p.pole_harmonic*p.lharm_h*np.sin(angles))
    return L,dL


def flux(p:Params,i,z,theta):
    L,_=matrices(p,theta)
    return L@i + p.saturation_h*p.saturation_a*np.tanh(i/p.saturation_a)+p.coupling_g*z


def invert_flux(p:Params,lam,z,theta):
    L,_=matrices(p,theta)
    i=np.linalg.solve(L,lam-p.coupling_g*z)
    for _ in range(35):
        f=L@i+p.saturation_h*p.saturation_a*np.tanh(i/p.saturation_a)+p.coupling_g*z-lam
        if np.linalg.norm(f,ord=np.inf)<2e-13:return i
        sech2=1-np.tanh(i/p.saturation_a)**2
        d=L+np.diag(p.saturation_h*sech2)
        i-=np.linalg.solve(d,f)
    raise RuntimeError('incremental inductance inverse did not converge')


def energy(p:Params,lam,z,theta):
    i=invert_flux(p,lam,z,theta)
    L,_=matrices(p,theta)
    q=i/p.saturation_a
    ac=np.abs(q)
    logcosh=ac+np.log1p(np.exp(-2*ac))-np.log(2)
    sat=p.saturation_h*p.saturation_a**2*np.sum(q*np.tanh(q)-logcosh)
    return float(.5*i@L@i+sat+.5*p.memory_h*z@z)


def energy_gradient(p:Params,lam,z,theta):
    i=invert_flux(p,lam,z,theta)
    return np.concatenate((i,-p.coupling_g*i+p.memory_h*z))


def discrete_gradient(p:Params,y0,y1,theta):
    """Gonzalez discrete gradient: exact energy secant by construction.

    GradU_bar dot (y1-y0) = U(y1)-U(y0) to roundoff; the correction
    is second order. For extremely small increments use the midpoint
    gradient; that regime is NOT an exact cancellation certificate.
    """
    d=y1-y0
    mid=.5*(y0+y1)
    g=energy_gradient(p,mid[:p.phases],mid[p.phases:],theta)
    dd=float(d@d)
    if dd<1e-22:return g
    du=energy(p,y1[:p.phases],y1[p.phases:],theta)-energy(p,y0[:p.phases],y0[p.phases:],theta)
    return g+((du-float(g@d))/dd)*d


def rational_wave_balance(incident=Fraction(7,3),current=Fraction(2,5),z0=Fraction(4),dt=Fraction(1,7)):
    """Exact signed scattering power: a²-r²=Z*v*i; v=2a-Zi."""
    refl=incident-z0*current
    voltage=incident+refl
    absorbed=dt*voltage*current
    removed=dt*(incident**2-refl**2)/z0
    assert absorbed==removed
    return dict(incident=str(incident),reflected=str(refl),absorbed_energy=str(absorbed),line_depletion=str(removed),equal=True)


def rational_lossy_waveguide_step():
    """Exact Fraction theorem for two-cell bidirectional *lossy* wave ledger."""
    s=Fraction(3,4)
    dt=Fraction(1,11)
    z0=Fraction(5,2)
    f=(Fraction(2),Fraction(7,3))
    b=(Fraction(-1,3),Fraction(4,5))
    launch=Fraction(3,2)
    cur=Fraction(-2,7)  # signed generator-port current is admissible
    incident=s*f[-1]
    returned=s*b[0]
    reflected=incident-z0*cur
    e0=dt/z0*sum(x*x for x in (*f,*b))
    e1=dt/z0*sum(x*x for x in (launch,s*f[0],s*b[1],reflected))
    src=dt/z0*(launch**2-returned**2)
    motor=dt*(incident+reflected)*cur
    loss=dt/z0*(1-s*s)*sum(x*x for x in (*f,*b))
    assert e1-e0==src-motor-loss
    assert loss>0
    return dict(e0=str(e0),e1=str(e1),source_work=str(src),motor_work=str(motor),
                dissipated=str(loss),exact=True,signed_motor_port=str(motor))


def step(p:Params,state,source_wave):
    """One causal full-line/memory-motor state step with energy receipt.

    Source wave is specified only from time/local returned wave, never from
    instantaneous remote machine state. Feedback via returned wave has >=2
    positive flight delays.
    """
    p.check()
    n=p.phases
    f=np.asarray(state['forward'],float)
    b=np.asarray(state['backward'],float)
    if f.shape!=(p.delay_cells,n) or b.shape!=(p.delay_cells,n):raise ValueError('invalid line state')
    outgoing=np.asarray(source_wave,float)
    if outgoing.shape!=(n,) or not np.all(np.isfinite(outgoing)):raise ValueError('invalid source-wave dimensions')
    s=p.line_transmission
    a=s*f[-1].copy()   # wave that has reached the *remote* terminal
    return_to_source=s*b[0].copy() # local return wave only
    theta=float(state['theta'])
    lam=np.asarray(state['flux'],float)
    z=np.asarray(state['memory'],float)
    y0=np.r_[lam,z]
    U0=energy(p,lam,z,theta)
    E0=p.dt_s/p.characteristic_ohm*(np.sum(f*f)+np.sum(b*b))
    i0=invert_flux(p,lam,z,theta)
    dz0=p.memory_mobility*(p.coupling_g*i0-p.memory_h*z)
    guess=np.r_[lam+p.dt_s*(2*a-(p.characteristic_ohm+p.resistance_ohm)*i0), z+p.dt_s*dz0]
    def residual(y):
        dg=discrete_gradient(p,y0,y,theta)
        cur=dg[:n]
        gz=dg[n:]
        return np.r_[y[:n]-lam-p.dt_s*(2*a-(p.characteristic_ohm+p.resistance_ohm)*cur),
                     y[n:]-z+p.dt_s*p.memory_mobility*gz]
    sol=root(residual,guess,method='hybr',options={'xtol':1e-10,'maxfev':350})
    if not np.linalg.norm(residual(sol.x),ord=np.inf)<2e-9:
        raise RuntimeError('implicit nonlinear boundary solve failed: '+str(sol.message))
    lam1=sol.x[:n].copy()
    z1=sol.x[n:].copy()
    dg=discrete_gradient(p,y0,sol.x,theta)
    cur=dg[:n]
    gz=dg[n:]
    reflected=a-p.characteristic_ohm*cur
    terminal_v=a+reflected
    motor_port=p.dt_s*float(terminal_v@cur)
    copper=p.dt_s*p.resistance_ohm*float(cur@cur)
    memory_diss=p.dt_s*p.memory_mobility*float(gz@gz)
    U1electrical=energy(p,lam1,z1,theta)
    theta1=theta+p.omega_rad_s*p.dt_s
    U1=energy(p,lam1,z1,theta1)
    shaft_extraction=U1-U1electrical
    source_work=p.dt_s/p.characteristic_ohm*float(outgoing@outgoing-return_to_source@return_to_source)
    f1=np.vstack((outgoing,s*f[:-1]))
    b1=np.vstack((s*b[1:],reflected))
    line_loss=p.dt_s/p.characteristic_ohm*(1-s*s)*float(np.sum(f*f)+np.sum(b*b))
    E1=p.dt_s/p.characteristic_ohm*(np.sum(f1*f1)+np.sum(b1*b1))
    residual_motor=U1-U0-(motor_port+shaft_extraction-copper-memory_diss)
    residual_line=E1-E0-(source_work-motor_port-line_loss)
    residual_joint=E1+U1-E0-U0-(source_work+shaft_extraction-copper-memory_diss-line_loss)
    return dict(state=dict(forward=f1,backward=b1,flux=lam1,memory=z1,theta=theta1),
                port_current=cur,incident=a,reflected=reflected,returned_source=return_to_source,
                source_work_j=source_work,motor_terminal_work_j=motor_port,
                shaft_mechanical_work_j=shaft_extraction,copper_loss_j=copper,
                memory_loss_j=memory_diss,line_loss_j=line_loss,line_energy_before_j=E0,line_energy_after_j=E1,
                motor_energy_before_j=U0,motor_energy_after_j=U1,
                residual_line_j=float(residual_line),residual_motor_j=float(residual_motor),
                residual_joint_j=float(residual_joint),implicit_residual_inf=float(np.linalg.norm(residual(sol.x),ord=np.inf)))


def initial(p:Params,current_a=0.,memory=0.):
    p.check()
    i=np.full(p.phases,current_a,float)
    z=np.full(p.phases,memory,float)
    return dict(forward=np.zeros((p.delay_cells,p.phases)),backward=np.zeros((p.delay_cells,p.phases)),
                flux=flux(p,i,z,0.),memory=z,theta=0.)


def run(p:Params=Params(),steps:int=35,drive_amplitude_v:float=1.1,local_reflection_gain:float=0.1):
    p.check()
    if steps<1 or not np.isfinite(drive_amplitude_v) or not 0<=local_reflection_gain<1:
        raise ValueError('invalid bounded local feedback')
    state=initial(p,current_a=.35,memory=.05)
    total=dict(source_work_j=0.,shaft_mechanical_work_j=0.,copper_loss_j=0.,memory_loss_j=0.,line_loss_j=0.)
    errors=[]
    solve_errors=[]
    pulses=[]
    for k in range(steps):
        # The only feedback input is the wave ALREADY at the source endpoint.
        source_response=state['backward'][0]
        launch=np.zeros(p.phases)
        if k==0:launch[0]=drive_amplitude_v
        if k==p.delay_cells+4:launch[1]=.5*drive_amplitude_v
        launch+=local_reflection_gain*source_response
        row=step(p,state,launch)
        for name in total:total[name]+=row[name]
        errors.append(max(abs(row['residual_line_j']),abs(row['residual_motor_j']),abs(row['residual_joint_j'])))
        solve_errors.append(row['implicit_residual_inf'])
        pulses.append(dict(k=k,incident0_v=float(row['incident'][0]),
                           source_return0_v=float(row['returned_source'][0]),
                           motor_port_w=float(row['motor_terminal_work_j']/p.dt_s)))
        state=row['state']
    final_energy=energy(p,state['flux'],state['memory'],state['theta']) + \
        p.dt_s/p.characteristic_ohm*(np.sum(state['forward']**2)+np.sum(state['backward']**2))
    initial_state=initial(p,current_a=.35,memory=.05)
    starting_energy=energy(p,initial_state['flux'],initial_state['memory'],0.)
    total['total_energy_change_j']=float(final_energy-starting_energy)
    total['integrated_balance_error_j']=float(total['total_energy_change_j']-(total['source_work_j']+total['shaft_mechanical_work_j']-total['copper_loss_j']-total['memory_loss_j']-total['line_loss_j']))
    return dict(model='constructed nonlinear multi-coil memory + lossy passive finite-speed waveguide with signed dynamic matching',
                assumptions=asdict(p),cable_m=p.cable_m,delay_s=p.delay_s,steps=steps,
                exact_wave_fraction=rational_wave_balance(),exact_lossy_packet_fraction=rational_lossy_waveguide_step(),cumulative=total,
                maximum_single_step_residual_j=float(max(errors)),
                max_implicit_residual_inf=float(max(solve_errors)),
                causal_trace=pulses,
                fails_to_prove=['same-object original V2 geometry/wiring','continuum Maxwell retarded PDE',
                                'arbitrary hysteresis, dissipation inside cable, semiconductor PWM',
                                'validated ODE/PDE existence and Agda kernel acceptance',
                                'steady device efficiency without shaft/auxiliary metrology'])

if __name__=='__main__':
    print(json.dumps(run(),indent=2))
