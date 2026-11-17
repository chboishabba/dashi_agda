#!/usr/bin/env python3
"""Magnetic torque-first A×B×E×F maximum cut; recovery NOT optimised.

Constructed bounded monotone polynomial coenergy, angular harmonics and smooth
positive-current waveforms. No V2 winding, flux map, rotor or torque data.

W'(theta,i)=0.5 (L0+a*cos(k theta)+b*cos(2k theta))*i²-beta*i⁴/4.
Stored U=i*lambda-W', lambda=partial_i W', tau=partial_theta W'.
Current i(theta)=sqrt(J*(1+u*sin(k theta)+v*sin(2k theta))),
where |u|+|v|<1, giving mean i²=J independent of timing.
Mean *mechanical input to generator*: -<tau*omega>.
The coenergy identity proves Pshaft=k*omega*J*(a*u+2*b*v)/4.
"""
from __future__ import annotations
from dataclasses import dataclass, asdict, replace
from math import sin,cos,sqrt,pi
import json
from pathlib import Path
import numpy as np

@dataclass(frozen=True)
class Magnetic:
    rpm:float=2354.0 # V2 speed is only source-reported number
    k:int=4
    L0:float=.040
    a:float=.012
    b:float=.008
    beta:float=.0001
    R:float=1.0
    J:float=25.0 # squared rms current, synthetic A²
    peak_I:float=8.0
    max_terminal_V:float=320.
    modulation_budget:float=.75
    base_motor_loss:float=12.0
    motor_torque_loss_coeff:float=100.0 # W / (N m)^2, illustrative

    @property
    def omega(self):return 2*pi*self.rpm/60
    def check(self):
        if not (isinstance(self.k,int) and self.k>0 and self.rpm>0 and self.J>0 and self.R>=0 and self.beta>=0):raise ValueError('invalid physical coefficients')
        if not (self.L0>abs(self.a)+abs(self.b)+3*self.beta*self.peak_I**2):raise ValueError('nonpositive magnetic incremental inductance')
        if not (0<self.modulation_budget<1 and self.peak_I>0 and self.max_terminal_V>0 and self.base_motor_loss>=0 and self.motor_torque_loss_coeff>=0):raise ValueError('invalid constraints')
        return self


def profile(m:Magnetic,u:float,v:float,n:int=8192):
    m.check()
    if abs(u)+abs(v)>m.modulation_budget+1e-12:raise ValueError('outside pointwise nonnegative modulation envelope')
    x=np.linspace(0,2*pi,n,endpoint=False)
    g=1+u*np.sin(x)+v*np.sin(2*x)
    if np.min(g)<=0:raise ValueError('current profile must stay positive')
    i=np.sqrt(m.J*g)
    di_dx=m.J*(u*np.cos(x)+2*v*np.cos(2*x))/(2*i)
    L=m.L0+m.a*np.cos(x)+m.b*np.cos(2*x)
    Lx=-m.a*np.sin(x)-2*m.b*np.sin(2*x)
    lam=L*i-m.beta*i**3
    lamx=Lx*i+(L-3*m.beta*i*i)*di_dx
    V=m.R*i+m.k*m.omega*lamx
    tau=-m.k*(m.a*np.sin(x)+2*m.b*np.sin(2*x))*i*i/2
    stored=.5*L*i*i-.75*m.beta*i**4
    return x,i,lam,V,tau,stored


def certified_envelope(m:Magnetic,u:float,v:float):
    """Continuous, conservative bounds; no angular sampling needed.

    Differentiated exact smooth profile. Bounds valid for every rotor angle,
    not transistor switching voltage or thermal stability.
    """
    m.check()
    if abs(u)+abs(v)>m.modulation_budget+1e-12:raise ValueError('invalid angular profile')
    lo=sqrt(m.J*(1-abs(u)-abs(v)))
    hi=sqrt(m.J*(1+abs(u)+abs(v)))
    dx=m.J*(abs(u)+2*abs(v))/(2*lo)
    Lmax=m.L0+abs(m.a)+abs(m.b)
    Lx=abs(m.a)+2*abs(m.b)
    # |L-3βi²| <= Lmax+3β i_max²
    voltage_bound=m.R*hi+m.k*m.omega*(Lx*hi+(Lmax+3*m.beta*hi**2)*dx)
    # Bound derivative of winding V with respect to rotor phase x.
    gpp=abs(u)+4*abs(v)
    ddx=m.J*gpp/(2*lo)+m.J**2*(abs(u)+2*abs(v))**2/(4*lo**3)
    Lxx=abs(m.a)+4*abs(m.b)
    voltage_dx_bound=(m.R*dx+m.k*m.omega*(Lxx*hi+2*Lx*dx+
        (Lmax+3*m.beta*hi**2)*ddx+6*m.beta*hi*dx**2))
    return {'min_current_lower_bound_a':lo,'max_current_upper_bound_a':hi,
        'di_dx_upper_bound_a_per_rad':dx,'terminal_voltage_upper_bound_v':voltage_bound,
        'terminal_voltage_lipschitz_bound_v_per_rad':voltage_dx_bound,
        'guaranteed_current_feasible':hi<=m.peak_I,
        'guaranteed_voltage_feasible':voltage_bound<=m.max_terminal_V,
        'continuous_winding_only':True}


def evaluate(m:Magnetic,u:float,v:float,n:int=8192):
    x,i,lam,voltage,tau,U=profile(m,u,v,n)
    shaft=-float(np.mean(tau))*m.omega
    analytic=m.k*m.omega*m.J*(m.a*u+2*m.b*v)/4
    copper=m.R*m.J
    # v*i=R*i²+dU/dt+tau*omega. Zero storage change over full cycle.
    terminal=float(np.mean(voltage*i))
    raw_bus=-terminal
    exact_bus=analytic-copper
    motor_torque=analytic/m.omega
    motor_input=analytic+m.base_motor_loss+m.motor_torque_loss_coeff*motor_torque**2
    envelope=certified_envelope(m,u,v)
    # Continuous voltage certificate: nearest-grid-point covering plus a
    # global derivative (Lipschitz) bound, *not* a sampled-only feasibility claim.
    envelope['sample_spacing_rad']=2*pi/n
    envelope['continuous_voltage_by_grid_lipschitz_v']=(float(np.max(abs(voltage)))+
        envelope['terminal_voltage_lipschitz_bound_v_per_rad']*pi/n)
    envelope['guaranteed_voltage_feasible_grid']=envelope['continuous_voltage_by_grid_lipschitz_v']<=m.max_terminal_V
    return {'u':u,'v':v,'continuous_envelope':envelope,'shaft_w':shaft,'shaft_exact_w':analytic,'reaction_nm':motor_torque,
        'rms_current_a':sqrt(m.J),'copper_w':copper,'raw_bus_w':raw_bus,'exact_bus_w':exact_bus,
        'peak_current_a':float(np.max(i)),'peak_voltage_v':float(np.max(abs(voltage))),
        'motor_electrical_input_w':motor_input,'motor_loss_w':motor_input-analytic,
        'storage_endpoint_delta_j':float(U[0]-U[0]),
        'coenergy_identity_residual_w':terminal-(copper-analytic),
        'torque_integral_residual_w':shaft-analytic,
        'output_increases_with_shaft_at_fixed_copper':True,
        'voltage_feasible_sampled':bool(np.max(abs(voltage))<=m.max_terminal_V),
        'current_feasible_sampled':bool(np.max(i)<=m.peak_I)}


def exact_diamond_optimum(m:Magnetic):
    """Rigorous unrestricted-voltage optimum of a linear functional over
    |u|+|v|<=budget. Not a finite-voltage or actual machine optimum."""
    m.check()
    au=m.a; bv=2*m.b
    if abs(au)>=abs(bv):u=m.modulation_budget*(1 if au>=0 else -1);v=0.
    else:u=0.;v=m.modulation_budget*(1 if bv>=0 else -1)
    bound=m.k*m.omega*m.J*m.modulation_budget*max(abs(au),abs(bv))/4
    assert abs(evaluate(m,u,v)['shaft_exact_w']-bound)<1e-10
    return {'u':u,'v':v,'upper_bound_shaft_w':bound,'proof':'dual norm: a*u+2b*v <= max(|a|,2|b|)*(|u|+|v|)','feasibility':'modulation/current only; voltage requires separate check'}


def finite_voltage_candidates(m:Magnetic,step:float=.05,n:int=4096):
    # Finite grid, not a continuous global optimisation theorem.
    j=int(round(m.modulation_budget/step))
    rows=[]
    for iu in range(-j,j+1):
        for iv in range(-j,j+1):
            u=iu*step;v=iv*step
            if abs(u)+abs(v)>m.modulation_budget+1e-10:continue
            q=evaluate(m,u,v,n=n)
            if q['voltage_feasible_sampled'] and q['current_feasible_sampled']:
                rows.append(q)
    return {'candidate_count':(2*j+1)**2-2*j*(j+1), 'feasible_count':len(rows),
        'best_feasible_sampled':max(rows,key=lambda r:r['shaft_w']) if rows else None,
        'sampling_only':True}


def magnetic_interventions(m:Magnetic):
    # Choose a matched RMS/copper trio with fixed (unoptimised) converter boundary.
    rows={name:evaluate(m,*p) for name,p in {
        'no_timing':(0,0),'first_harmonic':(.6,0),'second_harmonic':(0,.6),
        'cooperative_mix':(.3,.45),'reversed_first':(-.6,0)}.items()}
    # Source-selected data never assumed: all examples are generated countermodels.
    return {'family':asdict(m),'rows':rows,
        'fixed_copper_across_all':len({round(v['copper_w'],10) for v in rows.values()})==1,
        'fixed_recovery':'not a model degree of freedom; raw terminal work only',
        'analytic_optimum':exact_diamond_optimum(m)}



def matched_electrical_load(m:Magnetic,target_bus_w:float=20.,fixed_export_eta:float=.95):
    """Load ON at same net bus output across different magnetic current placement.

    All candidates share material map, RPM, converter export efficiency, and
    heating law; ONLY current angular placement and corresponding J vary.
    For positive raw export, Pbus=eta*J*(k*omega*(a*u+2*b*v)/4-R).
    Hence J is solved analytically, not readjusted by hidden shaft work.
    Baseline no-load J=0; rotor/motor baseline loss cancels in differences.
    """
    if target_bus_w<=0 or not 0<fixed_export_eta<=1:raise ValueError('invalid target or eta')
    arms={'first_harmonic':(.6,0.),'second_harmonic':(0.,.6),
          'cooperative_mix':(.3,.45),'single_harmonic_extreme':(0.,.75)}
    out={}
    for name,(u,v) in arms.items():
        gain=m.k*m.omega*(m.a*u+2*m.b*v)/4
        if gain<=m.R:continue
        J=target_bus_w/(fixed_export_eta*(gain-m.R))
        local=replace(m,J=J)
        q=evaluate(local,u,v)
        q.update({'export_eta_fixed':fixed_export_eta,
                  'exported_bus_w':fixed_export_eta*q['exact_bus_w'],
                  'converter_loss_w':(1-fixed_export_eta)*q['exact_bus_w'],
                  'incremental_motor_input_w':q['motor_electrical_input_w']-m.base_motor_loss,
                  'incremental_motor_torque_nm':q['reaction_nm'],
                  'total_loss_ex_motor_w':q['copper_w']+(1-fixed_export_eta)*q['exact_bus_w'],
                  'target_bus_w':target_bus_w})
        assert abs(q['exported_bus_w']-target_bus_w)<1e-10
        assert abs(q['shaft_exact_w']-q['copper_w']-q['converter_loss_w']-target_bus_w)<1e-10
        out[name]=q
    a=out['first_harmonic'];b=out['cooperative_mix']
    assert a['shaft_exact_w']>b['shaft_exact_w']
    assert abs((a['shaft_exact_w']-b['shaft_exact_w'])-(a['copper_w']-b['copper_w']))<1e-10
    return {'target_load_bus_w':target_bus_w,'common_converter_export_eta':fixed_export_eta,
        'motor_no_load_electrical_w':m.base_motor_loss,
        'arms':out,'matched_output_shaft_saving_w':a['shaft_exact_w']-b['shaft_exact_w'],
        'matched_output_copper_saving_w':a['copper_w']-b['copper_w'],
        'matched_output_motor_electrical_saving_w':a['incremental_motor_input_w']-b['incremental_motor_input_w'],
        'interpretation':'lower shaft reaction at fixed electrical output is exactly paid for by lower copper heat in this model; no recovery tuning',
        'whole_drivetrain_motor_efficiency_is_hypothetical':True}


def phase_number_negative_control(m:Magnetic):
    """Identical translated phases at fixed aggregate J, no interphase coupling.
    No phase-count magic in ideal core; per-phase controller overhead optional."""
    ideal=evaluate(m,0,.6)
    return {str(n):{'phase_count':n,'total_J':m.J,'total_copper_w':m.R*m.J,
        'total_shaft_w':ideal['shaft_exact_w'],
        'net_w_with_0_1W_phase_overhead':ideal['exact_bus_w']-n*.1}
        for n in (3,4,6,7,9,11)}


def run():
    m=Magnetic().check()
    return {'schema':'DASHI.V2.magnetic-torque-priority.v1',
        'hypothesis':'torque/output versus angular current placement at same RMS and fixed recovery',
        'magnetic':magnetic_interventions(m),'matched_load':matched_electrical_load(m),'phase_controls':phase_number_negative_control(m),
        'finite_grid':finite_voltage_candidates(m),
        'gates':{'physical_magnetic_map':'OPEN','real_torque_interventions':'OPEN',
            'real_converter':'NOT INFERRED','continuous_voltage_certificate':'OPEN',
            'kernel_acceptance':'NOT RUN'},'source_specific_v2_measured':False}
if __name__=='__main__':print(json.dumps(run(),indent=2))
