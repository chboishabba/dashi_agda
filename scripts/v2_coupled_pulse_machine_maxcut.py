#!/usr/bin/env python3
"""Source-independent reluctance generator: finite-bus, mutually coupled,
reversible saturation + passive magnetic-memory loss + 3-state pulse bridge.

Not the selected hardware of @madscience369, Don Smith, Filsinger, Holmstrom
or Infinity SAV. Signed power is independently integrated, not set equal to
mechanical extraction.  The state uses a stable convex magnetic energy:
 W'(i,theta,z)=.5*i^T L(theta)i + b*Is² sum log(cosh(i/Is))
                 + g*i.z - .5*h*z.z
 lambda = L*i+b*Is*tanh(i/Is)+g*z; fz=g*i-h*z;
 z_dot=mu*fz; U=i.lambda-W'=.5*iLi + reversible_saturation + .5*h*z.z
 i.lambda_dot = U_dot + tau*omega + mu*|fz|².

Finite bus |v|<=V by piecewise constant full-bridge command -V,0,+V.
A differential inequality bounds the *continuous* state between integration
points conditional on the specified T range and positive differential L.
RK4 is a numerical IVP check, NOT a validated ODE integrator or a global
optimality certificate. Pareto dominance is exhaustive ONLY on enumerated
candidate rows.  The original physical-instance gates remain OPEN.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass, replace
import json
import math
import sys
from pathlib import Path

import numpy as np


@dataclass(frozen=True)
class Machine:
    rpm: float = 2354.0                  # Only this approximate value occurs in V2 reel
    pole_harmonic: int = 4                # Invented motor geometry
    l0_h: float = .040
    lharm_h: float = .012
    mutual_h: float = .0012              # Neighbour flux link
    saturation_h: float = .004           # Positive, decreasing incremental slope
    saturation_a: float = 5.0
    lag_flux_h: float = .003
    lag_energy_h: float = .003
    lag_mobility: float = 12000.0
    r_ohm: float = 1.0
    r_temp_coeff: float = .0039
    bus_v: float = 320.0
    current_limit_a: float = 22.0
    ambient_c: float = 25.0
    thermal_limit_c: float = 95.0
    thermal_capacity_j_per_k: float = 25.0
    cooling_w_per_k: float = 1.0
    eta_forward: float = .985
    eta_reverse: float = .985
    switching_fixed_j: float = .00004
    switching_i2_j_per_a2: float = .000001
    static_converter_w: float = .15
    pwm_hz: float = 20000.0
    tracking_gain_ohm: float = 8.0
    control_stride: int = 4
    steps_per_rev: int = 180
    warmup_revs: int = 1
    measured_revs: int = 1

    @property
    def omega(self):
        return 2 * math.pi * self.rpm / 60

    def validate(self):
        if not (self.l0_h - abs(self.lharm_h) - 2 * abs(self.mutual_h) > 0):
            raise ValueError("positive differential inductance Gershgorin bound required")
        if not (0 < self.eta_forward <= 1 and 0 < self.eta_reverse <= 1):
            raise ValueError("invalid converter efficiency")
        for x in (self.rpm, self.saturation_a, self.bus_v, self.current_limit_a,
                  self.thermal_capacity_j_per_k, self.steps_per_rev,
                  self.control_stride, self.measured_revs, self.r_ohm):
            if x <= 0: raise ValueError("nonpositive machine parameter")
        for x in (self.saturation_h,self.lag_flux_h,self.lag_energy_h,
                  self.lag_mobility,self.mutual_h,self.r_temp_coeff,
                  self.cooling_w_per_k,self.switching_fixed_j,
                  self.switching_i2_j_per_a2,self.static_converter_w):
            if x < 0: raise ValueError("negative dissipative/constitutive parameter")
        if self.thermal_limit_c <= self.ambient_c or self.pole_harmonic < 1:
            raise ValueError("invalid material/thermal bound")


def matrices(p:Machine, m:int, theta:float):
    if m < 3: raise ValueError("test requires at least three phases")
    angle=p.pole_harmonic*theta - 2*math.pi*np.arange(m)/m
    diag=p.l0_h + p.lharm_h*np.cos(angle)
    L=np.diag(diag)
    for j in range(m):
        k=(j+1)%m
        if k!=j:
            L[j,k]+=p.mutual_h
            L[k,j]+=p.mutual_h
    dL=np.diag(-p.pole_harmonic*p.lharm_h*np.sin(angle))
    return L,dL,angle


def magnetic(p:Machine, i:np.ndarray, z:np.ndarray, theta:float):
    L,dL,_=matrices(p,len(i),theta)
    t=np.tanh(i/p.saturation_a)
    x=np.abs(i/p.saturation_a)
    logcosh=x+np.log1p(np.exp(-2*x))-math.log(2)
    co=.5*float(i@L@i)+p.saturation_h*p.saturation_a**2*float(np.sum(logcosh)) \
       +p.lag_flux_h*float(i@z)-.5*p.lag_energy_h*float(z@z)
    lam=L@i+p.saturation_h*p.saturation_a*t+p.lag_flux_h*z
    field_energy=float(i@lam-co)
    tau=.5*float(i@dL@i)
    return dict(flux=lam,energy_j=field_energy,torque_nm=tau,
                incremental=L+np.diag(p.saturation_h/(np.cosh(i/p.saturation_a)**2)),
                dL=dL,coenergy_j=co)


def majorant(p:Machine, i:np.ndarray,z:np.ndarray, dt:float,m:int):
    """Analytic Gronwall upper bound on max(|i(t)|,|z(t)|) over one step.
    Conditional on ambient<=T<=Tlimit; thermal bound checked separately.
    No interpolation or sampled-only current supremum is substituted.
    """
    lower=p.l0_h-abs(p.lharm_h)-2*abs(p.mutual_h)
    rmax=p.r_ohm*(1+p.r_temp_coeff*(p.thermal_limit_c-p.ambient_c))
    k,h,mu=p.lag_flux_h,p.lag_energy_h,p.lag_mobility
    alpha=max((rmax+abs(p.omega)*abs(p.lharm_h)*p.pole_harmonic
               +k*mu*(k+h))/lower, mu*(k+h))
    beta=p.bus_v/lower
    x0=max(float(np.max(np.abs(i))),float(np.max(np.abs(z))))
    upper=(x0+beta/alpha)*math.exp(alpha*dt)-beta/alpha
    return float(upper)


def simulate(p:Machine,m:int,peak_a:float,q:float,lead:float=0.,
             fixed_copper_mass:bool=False, controller_mode:str='relay'):
    """controller_mode='relay': exact three-state bridge with finite dwell.
    controller_mode='pwm_tracking': held averaged PWM duty voltage, whose
    carrier switching loss is counted explicitly; not exact semiconductor PWM.
    """
    p.validate()
    if controller_mode not in ('relay','pwm_tracking'):
        raise ValueError("unknown controller mode")
    if m < 3 or peak_a <= 0 or not (0 <= q < 1):
        raise ValueError("bad phase or pulse controls")
    # Fixed total copper mass surrogate: equal turns/length but conductor area per
    # phase ~1/m, so winding resistance ~m.  Does not assert identical L in reality.
    winding_r=p.r_ohm*(m/3 if fixed_copper_mass else 1.0)
    dt=(2*math.pi/p.omega)/p.steps_per_rev
    total=(p.warmup_revs+p.measured_revs)*p.steps_per_rev
    warm=p.warmup_revs*p.steps_per_rev
    theta=0.0
    i=np.zeros(m)
    z=np.zeros(m)
    T=p.ambient_c
    command=np.zeros(m)
    switching_count=0
    switch_energy=0.0
    integral=np.zeros(7) # shaft,cu,hys,coil drive,coil regen,cool,controller heat
    start_state=None
    min_diff=p.l0_h-abs(p.lharm_h)-2*abs(p.mutual_h)
    max_current_bound=0.0
    max_terminal=0.
    max_temp_bound=p.ambient_c
    max_temp=p.ambient_c
    torque_samples=[]
    for step in range(total):
        if step==warm:
            integral=np.zeros(7)
            switching_count=0
            switch_energy=0.0
            max_current_bound=0.
            max_temp_bound=T
            start_state=(i.copy(),z.copy(),T,theta)
        if controller_mode=='pwm_tracking' or step%p.control_stride==0:
            _,_,angle=matrices(p,m,theta)
            demand=np.maximum(np.sin(angle+lead),0)
            demand=np.where(np.sin(angle+lead)>q, demand,0)
            target=peak_a*math.sqrt(3/m)*demand**1.5
            error=target-i
            if controller_mode=='relay':
                newcommand=np.where(error>.11,p.bus_v,np.where(error<-.11,-p.bus_v,0.))
                if step >= warm:
                    switched=np.where(newcommand != command)[0]
                    switching_count+=len(switched)
                    event=float(np.sum(p.switching_fixed_j+p.switching_i2_j_per_a2*i[switched]**2))
                    switch_energy+=event
                    T+=event/p.thermal_capacity_j_per_k
            else:
                # PWM AVERAGE: a bounded duty ratio of a full bridge, not an
                # instantaneous continuous physical transistor command.
                mag=magnetic(p,i,z,theta)
                pulse=np.maximum(np.sin(angle+lead)-q,0)
                target=peak_a*math.sqrt(3/m)*pulse*pulse
                dtarget=peak_a*math.sqrt(3/m)*2*pulse*np.cos(angle+lead)*p.pole_harmonic*p.omega
                zd=p.lag_mobility*(p.lag_flux_h*i-p.lag_energy_h*z)
                R=winding_r*(1+p.r_temp_coeff*(T-p.ambient_c))
                fwd=R*i+mag['incremental']@dtarget +mag['dL']@i*p.omega+p.lag_flux_h*zd
                newcommand=np.clip(fwd+p.tracking_gain_ohm*(target-i),-p.bus_v,p.bus_v)
                if step>=warm:
                    # Idealised 2 switch transitions / PWM period on every
                    # nonzero active phase. Gate work is not free.
                    active=np.abs(newcommand)>1e-9
                    count=float(active.sum())*2*p.pwm_hz*dt
                    event=float(np.sum((p.switching_fixed_j+p.switching_i2_j_per_a2*i[active]**2)))*2*p.pwm_hz*dt
                    switching_count+=count
                    switch_energy+=event
                    T+=event/p.thermal_capacity_j_per_k
            command=newcommand
        max_terminal=max(max_terminal,float(np.max(np.abs(command))))
        # Integrated energies directly from ODE powers, independent of U endpoint.
        def ode(th,ii,zz,temp):
            mag=magnetic(p,ii,zz,th)
            fz=p.lag_flux_h*ii-p.lag_energy_h*zz
            zd=p.lag_mobility*fz
            R=winding_r*(1+p.r_temp_coeff*(temp-p.ambient_c))
            did=np.linalg.solve(mag['incremental'],command-R*ii-mag['dL']@ii*p.omega-p.lag_flux_h*zd)
            pc=float(R*np.dot(ii,ii))
            ph=float(p.lag_mobility*np.dot(fz,fz))
            ps=command*ii
            drive=float(np.maximum(ps,0).sum())
            regen=float(np.maximum(-ps,0).sum())
            cool=p.cooling_w_per_k*max(temp-p.ambient_c,0.)
            td=(pc+ph-cool)/p.thermal_capacity_j_per_k
            rates=np.array([-mag['torque_nm']*p.omega,pc,ph,drive,regen,cool,pc+ph])
            return did,zd,td,rates
        k1=ode(theta,i,z,T)
        k2=ode(theta+.5*p.omega*dt,i+.5*dt*k1[0],z+.5*dt*k1[1],T+.5*dt*k1[2])
        k3=ode(theta+.5*p.omega*dt,i+.5*dt*k2[0],z+.5*dt*k2[1],T+.5*dt*k2[2])
        k4=ode(theta+p.omega*dt,i+dt*k3[0],z+dt*k3[1],T+dt*k3[2])
        new_i=i+dt*(k1[0]+2*k2[0]+2*k3[0]+k4[0])/6
        new_z=z+dt*(k1[1]+2*k2[1]+2*k3[1]+k4[1])/6
        new_T=T+dt*(k1[2]+2*k2[2]+2*k3[2]+k4[2])/6
        if step>=warm:
            integral+=dt*(k1[3]+2*k2[3]+2*k3[3]+k4[3])/6
            torque_samples.append(magnetic(p,i,z,theta)['torque_nm'])
            bound=majorant(replace(p,r_ohm=winding_r),i,z,dt,m)
            max_current_bound=max(max_current_bound,bound)
            # Upper bound uses nonnegative heat and ignores cooling; valid so
            # long as temperature remains >=ambient and below the declared cap.
            rmax=winding_r*(1+p.r_temp_coeff*(p.thermal_limit_c-p.ambient_c))
            heat_upper=m*rmax*bound*bound + m*p.lag_mobility*(p.lag_flux_h+p.lag_energy_h)**2*bound**2
            max_temp_bound=max(max_temp_bound,T+dt*heat_upper/p.thermal_capacity_j_per_k)
        i,z,T=new_i,new_z,new_T
        theta+=p.omega*dt
        max_temp=max(max_temp,T)
    assert start_state is not None
    i0,z0,T0,theta0=start_state
    delta_u=magnetic(p,i,z,theta)['energy_j']-magnetic(p,i0,z0,theta0)['energy_j']
    shaft,cu,hys,drive,regen,cool,heat=integral
    total_time=p.measured_revs*2*math.pi/p.omega
    coil_net=regen-drive
    electronics_loss=(1-p.eta_reverse)*regen+(1/p.eta_forward-1)*drive
    idle=p.static_converter_w*total_time
    bus=regen*p.eta_reverse-drive/p.eta_forward-switch_energy-idle
    converter_loss=electronics_loss+switch_energy+idle
    balance_residual=shaft-(coil_net+cu+hys+delta_u)
    bus_residual=shaft-(bus+converter_loss+cu+hys+delta_u)
    thermal_endpoint=p.thermal_capacity_j_per_k*(T-T0)
    thermal_residual=thermal_endpoint-(cu+hys+switch_energy-cool)
    current_state_delta=float(np.max(np.abs(i-i0)))
    lag_state_delta=float(np.max(np.abs(z-z0)))
    state_scale=max(1.,float(np.max(np.abs(i))),float(np.max(np.abs(i0))),
                       float(np.max(np.abs(z))),float(np.max(np.abs(z0))))
    full_state_near_periodic=bool(current_state_delta<=.02*state_scale and lag_state_delta<=.02*state_scale
                                   and abs(delta_u)<=.02*max(abs(shaft),1e-12))
    ts=np.asarray(torque_samples)
    torque_ripple=float(np.std(ts)/(abs(np.mean(ts))+1e-12))
    feasible=(max_terminal<=p.bus_v+1e-9 and max_current_bound<=p.current_limit_a
              and max_temp_bound<=p.thermal_limit_c
              and min_diff>0 and T>=p.ambient_c-1e-8)
    return dict(m=m,peak_a=peak_a,q=q,lead=lead,fixed_copper_mass=fixed_copper_mass,controller_mode=controller_mode,
                feasible=bool(feasible),power_bus_w=bus/total_time,
                power_mechanical_extract_w=shaft/total_time,
                power_copper_w=cu/total_time,power_hysteresis_w=hys/total_time,
                power_switch_w=switch_energy/total_time,
                power_converter_w=converter_loss/total_time,
                power_cooling_w=cool/total_time,
                power_storage_change_w=delta_u/total_time,
                storage_adjusted_bus_w=(bus+delta_u)/total_time,
                storage_drift_fraction=abs(delta_u)/max(abs(shaft),1e-12),
                energy_inventory_stable_2pct=bool(abs(delta_u)<=.02*max(abs(shaft),1e-12)),
                magnetically_periodic_2pct=full_state_near_periodic,
                current_state_delta_a=current_state_delta,lag_state_delta=lag_state_delta,
                thermal_endpoint_change_c=T-T0,
                gross_drive_w=drive/total_time,gross_regen_w=regen/total_time,
                max_voltage_v=max_terminal,
                max_current_continuous_majorant_a=max_current_bound,
                observed_sample_current_a=float(np.max(np.abs(i))),
                thermal_continuous_majorant_c=max_temp_bound,max_temp_sample_c=max_temp,
                terminal_temp_c=T,torque_ripple=torque_ripple,
                switch_events=switching_count,
                energy_residual_j=balance_residual,bus_energy_residual_j=bus_residual,
                thermal_energy_residual_j=thermal_residual,
                measured_time_s=total_time,
                note='RK4 ODE with conditional analytic state majorants; no validated numerical IVP error proof')



def symbolic_multicoil_identity():
    """Exact SymPy proof: saturation, varying mutual L, passive lag state.
    Two coils suffice to test every cross-term of the quadratic L matrix.
    The identity is general in i, z, theta and their time derivatives.
    """
    import sympy as sy
    i1,i2,z1,z2,di1,di2,dz1,dz2,th,w = sy.symbols(
        'i1 i2 z1 z2 di1 di2 dz1 dz2 th omega',real=True)
    a,l0,m,b,Is,g,h,k=sy.symbols('a l0 m b Is g h k',real=True,positive=True)
    i=[i1,i2];z=[z1,z2]
    L=sy.Matrix([[l0+a*sy.cos(k*th),m],[m,l0-a*sy.cos(k*th)]])
    iv=sy.Matrix(i)
    co=sy.Rational(1,2)*(iv.T*L*iv)[0]+b*Is**2*sum(sy.log(sy.cosh(x/Is)) for x in i)
    co+=g*(i1*z1+i2*z2)-sy.Rational(1,2)*h*(z1**2+z2**2)
    flux=[sy.diff(co,x) for x in i]
    field=i1*flux[0]+i2*flux[1]-co
    torque=sy.diff(co,th)
    forces=[sy.diff(co,x) for x in z]
    def dt(expr):
        return (sy.diff(expr,th)*w+sy.diff(expr,i1)*di1
                +sy.diff(expr,i2)*di2+sy.diff(expr,z1)*dz1
                +sy.diff(expr,z2)*dz2)
    residual=sy.simplify(i1*dt(flux[0])+i2*dt(flux[1])-dt(field)
                         -torque*w-forces[0]*dz1-forces[1]*dz2)
    assert residual==0
    return dict(residual=str(residual),identity='i.dlambda = dU + tau.dtheta + fz.dz',
                memory_dissipation='mu*(fz1**2+fz2**2)>=0 for mu>=0',
                source='constructed model; exact symbolic identity only')


def dominates(a:dict,b:dict,tol:float=1e-10)->bool:
    """Finite dominance: higher storage-adjusted output, lower ripple/heat/cost."""
    good=(a['storage_adjusted_bus_w']>=b['storage_adjusted_bus_w']-tol
          and a['torque_ripple']<=b['torque_ripple']+tol
          and a['max_temp_sample_c']<=b['max_temp_sample_c']+tol
          and a['m']<=b['m'])
    strict=(a['storage_adjusted_bus_w']>b['storage_adjusted_bus_w']+tol
            or a['torque_ripple']<b['torque_ripple']-tol
            or a['max_temp_sample_c']<b['max_temp_sample_c']-tol
            or a['m']<b['m'])
    return good and strict


def frontier(rows:list[dict])->list[dict]:
    feasible=[r for r in rows if r['feasible']]
    return [x for x in feasible if not any(dominates(y,x) for y in feasible if y is not x)]


def fixed_shaft_comparison(p:Machine=Machine(), target_w:float=120., m_values=range(3,13),
                           q=.45,lead=.18):
    """Independent source-accounted amplitude search: mechanical input matched
    to a stated TARGET, rather than making a misleading fixed-current comparison.
    Only grid-certified closeness is claimed; relay dynamics can be discontinuous
    in amplitude, so no monotonicity or continuous global optimum is assumed.
    """
    if target_w<=0:raise ValueError("target shaft extraction must be positive")
    rows=[]
    for m in m_values:
        candidates=[simulate(p,m,float(amp),q,lead,True)
                    for amp in np.linspace(2,9,29)]
        candidate=min((r for r in candidates if r['feasible']),
                      key=lambda r:(abs(r['power_mechanical_extract_w']-target_w),
                                    -r['power_bus_w']),default=None)
        if candidate is None:continue
        row=dict(candidate)
        row['shaft_target_w']=target_w
        row['shaft_mismatch_w']=row['power_mechanical_extract_w']-target_w
        row['shaft_within_5pct']=bool(abs(row['shaft_mismatch_w'])<=.05*target_w)
        row['physical_efficiency_rank_admissible']=bool(row['shaft_within_5pct'] and row['magnetically_periodic_2pct'])
        rows.append(row)
    return rows


def run(max_phases:int=12):
    p=Machine()
    results=[]
    for m in range(3,max_phases+1):
        for q in (0.0,.45):
            for lead in (0.,.18):
                results.append(simulate(p,m,7.,q,lead,fixed_copper_mass=True))
    f=frontier(results)
    matched=fixed_shaft_comparison(p,m_values=range(3,max_phases+1))
    pwm=[simulate(replace(p,warmup_revs=5),m,14,.45,.18,True,controller_mode='pwm_tracking')
         for m in range(3,max_phases+1)]
    return dict(source='constructed source-independent V2 motor analogue, NOT apparatus reconstruction',
                symbolic_multicoil=symbolic_multicoil_identity(),
                assumptions=asdict(p),candidate_count=len(results),feasible_count=sum(r['feasible'] for r in results),
                frontier_count=len(f),frontier=f,all_candidates=results,
                electrically_feasible_but_nonperiodic=sum(r['feasible'] and not r['magnetically_periodic_2pct'] for r in results),
                finite_dominance_uses='storage_adjusted_bus_w, torque_ripple, peak temperature, count',
                matched_shaft_target_w=120.,matched_shaft_candidates=matched,
                stationary_pwm_candidates=pwm,
                pwm_magnetic_state_matched=sum(r['magnetically_periodic_2pct'] for r in pwm),
                matched_within_5pct=sum(r['shaft_within_5pct'] for r in matched),
                matched_stationary_2pct=sum(r['physical_efficiency_rank_admissible'] for r in matched),
                max_energy_residual_j=max(abs(r['energy_residual_j']) for r in results),
                max_thermal_residual_j=max(abs(r['thermal_energy_residual_j']) for r in results),
                proof_scope='finite-grid exhaustive dominance only; pointwise voltage exactly in allowed 3-state set, conditional Gronwall majorant; RK4 not rigorous flow enclosure')

if __name__=='__main__':
    print(json.dumps(run(max_phases=int(sys.argv[1]) if len(sys.argv)>1 else 12),indent=2))
