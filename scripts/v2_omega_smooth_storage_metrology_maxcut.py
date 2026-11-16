#!/usr/bin/env python3
"""V2 A-H/Omega next cut: independent smooth magnetic / bus-cycle / experiment audit.

ALL parameters except approximate source-reported rpm are synthetic. The smooth
current is a manufactured feedforward waveform with finite continuous v(t),
not the original V2 transistor-resolved implementation or a proof of tracking.
Bus load is an ideal constant-power extraction with a physical capacitor
inventory that closes after a cycle; controller/thermal inventories are distinct.
"""
from __future__ import annotations
from dataclasses import asdict, dataclass, replace
import json, math
from pathlib import Path
import numpy as np
from scipy.optimize import brentq


@dataclass(frozen=True)
class Plant:
    rpm: float=2354.0                         # reported reel speed, not verified
    shaft_w: float=45.0                       # *assumed* generator shaft extraction
    pole_harmonic: int=4                     # invented
    L0_h: float=.04
    A_h: float=.012
    Is_a: float=5.0
    R_ohm: float=1.0
    Vlim_v: float=320.0
    Ilim_a: float=22.0
    slew_lim_a_s: float=35000.0
    eta_forward: float=.98
    eta_reverse: float=.95
    bridge_loss_w: float=.30
    core_loss_w: float=.5
    control_loss_w: float=.2
    capacitor_f: float=.010
    bus_initial_v: float=340.0
    bus_min_v: float=330.0
    bus_max_v: float=360.0
    n: int=16384

    def validate(self):
        if not (0<self.A_h<self.L0_h and self.Is_a>0 and self.R_ohm>0 and self.Vlim_v>0 and self.Ilim_a>0 and self.slew_lim_a_s>0 and self.capacitor_f>0 and self.bus_initial_v>0 and self.n>=256 and self.pole_harmonic>=1 and self.rpm>0 and self.shaft_w>0):
            raise ValueError('invalid physical benchmark')
        if not (0<self.eta_forward<=1 and 0<self.eta_reverse<=1 and 0<self.bus_min_v<self.bus_initial_v<self.bus_max_v):
            raise ValueError('invalid passive conversion or bus bounds')
        if min(self.bridge_loss_w,self.core_loss_w,self.control_loss_w)<0:raise ValueError('negative parasitic work')

    @property
    def omega(self):return 2*math.pi*self.rpm/60


def _logcosh(x):return np.logaddexp(x,-x)-math.log(2)


def shape(x:np.ndarray,q:float,lead:float):
    """C1 finite-slew gate: i=I max(sin(x+lead)-q,0)^2."""
    z=np.sin(x+lead)-q
    on=np.maximum(z,0.)
    return on*on,2*on*np.cos(x+lead)


def profile(p:Plant,q:float,lead:float=0.,eta_reverse:float|None=None,
            control_extra_w:float=0.,require_feasible:bool=True)->dict:
    p.validate()
    if not (0<=q<1 and abs(lead)<=math.pi/3 and control_extra_w>=0):raise ValueError('invalid pulse')
    eta=p.eta_reverse if eta_reverse is None else eta_reverse
    if not 0<eta<=1: raise ValueError('invalid reverse converter')
    x=2*math.pi*np.arange(p.n)/p.n
    f,df=shape(x,q,lead)
    if np.all(f==0):raise ValueError('zero shaft response')
    wp=p.pole_harmonic*p.omega
    def mechanical(scale):
        i=scale*f
        torque=-p.A_h*p.pole_harmonic*p.Is_a**2*_logcosh(i/p.Is_a)*np.sin(x)
        return float(np.mean(-torque*p.omega))
    if mechanical(200.)<p.shaft_w:raise ValueError('cannot match shaft input')
    scale=brentq(lambda a:mechanical(a)-p.shaft_w,0.,200.,xtol=1e-11)
    i=scale*f
    didt=scale*wp*df
    lambda_i=p.L0_h+p.A_h*np.cos(x)/(np.cosh(i/p.Is_a)**2)
    lambda_theta_omega=-p.A_h*np.sin(x)*p.Is_a*np.tanh(i/p.Is_a)*wp
    v=p.R_ohm*i+lambda_i*didt+lambda_theta_omega
    flux=p.L0_h*i+p.A_h*np.cos(x)*p.Is_a*np.tanh(i/p.Is_a)
    U=i*flux-(.5*p.L0_h*i*i+p.A_h*np.cos(x)*p.Is_a**2*_logcosh(i/p.Is_a))
    torque=-p.A_h*p.pole_harmonic*p.Is_a**2*_logcosh(i/p.Is_a)*np.sin(x)
    shaft=float(np.mean(-torque*p.omega))
    copper=float(np.mean(p.R_ohm*i*i))
    coil=v*i
    # Signed power: positive coil terminal consumption / negative generation.
    p_fwd=np.maximum(coil,0.)
    p_rev=np.maximum(-coil,0.)
    bus_inst=eta*p_rev-p_fwd/p.eta_forward-p.bridge_loss_w-p.core_loss_w-p.control_loss_w-control_extra_w
    out=float(np.mean(bus_inst))
    ideal=float(np.mean(-coil))
    # Negative port work, copper and shaft are related by zero stored-cycle endpoints.
    eqres=shaft-copper-ideal
    converter_loss=float(np.mean(p_rev*(1-eta)+p_fwd*(1/p.eta_forward-1)))
    parasitic=p.bridge_loss_w+p.core_loss_w+p.control_loss_w+control_extra_w
    full_res=shaft-(out+copper+converter_loss+parasitic)
    period=2*math.pi/p.omega
    dt=period/p.n
    # Energy reservoir: one physical cycle of net converter-port power and an
    # ideal constant-power sink; exactly enforce discrete matching via mean.
    dE=(bus_inst-out)*dt
    E0=.5*p.capacitor_f*p.bus_initial_v**2
    E=E0+np.r_[0,np.cumsum(dE)]
    bus_v=np.sqrt(2*E/p.capacitor_f) if np.min(E)>0 else np.zeros_like(E)
    stored_periodic=(abs(U[-1]-U[0])<1e-3) # sampled points are not endpoints!
    # exact periodic samples x=0 and x=2pi by analytic extension; U(0)==U(2pi).
    endpoints_exact_by_periodicity=True
    metrics={
        'q':float(q),'lead_rad':float(lead),'scale_a':float(scale),'shaft_w':shaft,
        'net_bus_w':out,'copper_w':copper,'converter_loss_w':converter_loss,
        'controller_and_core_w':parasitic,'gross_forward_w':float(np.mean(p_fwd)),
        'gross_reverse_w':float(np.mean(p_rev)),
        'mean_signed_coil_w':float(np.mean(coil)),
        'peak_current_a':float(np.max(np.abs(i))),
        'peak_terminal_voltage_v':float(np.max(np.abs(v))),
        'peak_current_slew_a_s':float(np.max(np.abs(didt))),
        'min_dc_bus_v':float(np.min(bus_v)),'max_dc_bus_v':float(np.max(bus_v)),
        'bus_energy_endpoint_residual_j':float(E[-1]-E[0]),
        'windings_periodic_by_analytic_waveform':endpoints_exact_by_periodicity,
        'storage_rate_w':0.0,
        'magnetic_signed_energy_residual_w':float(eqres),
        'total_signed_energy_residual_w':float(full_res),
        'capacitor_joules_start':float(E[0]),
        'capacitor_joules_end':float(E[-1]),
        'sampled_approximation':f'{p.n} uniform rotor phase samples, not validated continuous integrals',
    }
    feasible=(metrics['peak_current_a']<=p.Ilim_a and
              metrics['peak_terminal_voltage_v']<=p.Vlim_v and
              metrics['peak_current_slew_a_s']<=p.slew_lim_a_s and
              metrics['min_dc_bus_v']>=p.bus_min_v and metrics['max_dc_bus_v']<=p.bus_max_v)
    metrics['sampled_feasible']=bool(feasible)
    # Continuous *global* supersets: |f| <= (1-q)^2, |f'| <= 2(1-q)
    # |lambda_i| <= L0+A, |∂t lambda(theta)| <= A*Is*kω,
    # |v| <= R Imax + (L0+A) di/dt max + A Is kω.
    imax=scale*(1-q)**2
    slewb=2*scale*(1-q)*wp
    vb=p.R_ohm*imax+(p.L0_h+p.A_h)*slewb+p.A_h*p.Is_a*wp
    metrics['analytic_current_upper_a']=float(imax)
    metrics['analytic_slew_upper_a_s']=float(slewb)
    metrics['analytic_voltage_upper_v']=float(vb)
    # Analytic derivative upper bound: |dv/dx|<=M over the entire phase.
    # With a uniform phase grid, any x lies at distance <=pi/n from a sample.
    # Thus max|v| <= max sampled |v| + M*pi/n, independent of point selection.
    ix=2*scale*(1-q)
    ixx=2*scale*(1+(1-q))
    dv_dx=(p.R_ohm*ix +(p.L0_h+p.A_h)*ixx*wp
           +(2*p.A_h*ix+2*p.A_h*ix*ix/p.Is_a)*wp+p.A_h*p.Is_a*wp)
    vc=float(np.max(np.abs(v))+dv_dx*math.pi/p.n)
    metrics['analytic_voltage_derivative_bound_v_per_rad']=float(dv_dx)
    metrics['continuous_voltage_grid_lipschitz_upper_v']=vc
    metrics['continuous_winding_envelope_certified']=bool(imax<=p.Ilim_a and slewb<=p.slew_lim_a_s and vc<=p.Vlim_v)
    # LC/bus charge is not added as an independent power source. Its load is
    # defined by the exact continuous-cycle mean of net converter power; the
    # numerical quadrature approximates that integral with an explicit bound.
    # p_bus(x) is Lipschitz, including through reversals via max(0,+/-coil).
    Pcoef=max(eta,1/p.eta_forward)
    dvbound=max(abs(v))+dv_dx*math.pi/p.n
    ibound=imax
    coil_dx_bound=dv_dx*ibound+dvbound*ix
    bus_dx_bound=Pcoef*coil_dx_bound
    mean_quad_bound_w=bus_dx_bound*math.pi/p.n
    metrics['bus_mean_quadrature_error_upper_w']=float(mean_quad_bound_w)
    metrics['coil_abs_power_lipschitz_upper_w_per_rad']=float(coil_dx_bound)
    # With continuous exact load Pbar, the energy error of quadrature steps
    # is bounded by T*(2*mean-error bound) plus an intra-step travel bound.
    sup_power=Pcoef*dvbound*ibound+parasitic
    gap_energy=(period*(2*mean_quad_bound_w)
                +(sup_power+abs(out)+mean_quad_bound_w)*dt)
    Emin=float(np.min(E)-gap_energy)
    Emax=float(np.max(E)+gap_energy)
    metrics['continuous_dc_bus_energy_lower_j']=Emin
    metrics['continuous_dc_bus_energy_upper_j']=Emax
    metrics['continuous_dc_bus_enclosure_certified']=bool(Emin>=.5*p.capacitor_f*p.bus_min_v**2 and Emax<=.5*p.capacitor_f*p.bus_max_v**2)
    metrics['continuous_bus_and_thermal_certified']=False # thermal state unmodelled
    if require_feasible and not feasible:
        raise ValueError('sampled electrical/bus limit infeasible')
    return metrics


def frontier(p:Plant)->dict:
    candidates=[]
    for q in (0.,.15,.30,.45,.60):
        for lead in (-.15,0.,.15):
            for eta,control_extra,name in ((.95,0.,'ordinary_recovery'),(.99,.4,'enhanced_recovery')):
                try:r=profile(p,q,lead,eta,control_extra,require_feasible=False)
                except ValueError:continue
                r['mode']=name
                candidates.append(r)
    baseline=next(r for r in candidates if r['q']==0 and r['lead_rad']==0 and r['mode']=='ordinary_recovery')
    feasible=[r for r in candidates if r['sampled_feasible']]
    certified=[r for r in feasible if r['continuous_winding_envelope_certified']]
    enhanced=next(r for r in candidates if r['q']==0 and r['lead_rad']==0 and r['mode']=='enhanced_recovery')
    gain=enhanced['net_bus_w']-baseline['net_bus_w']
    # Both cases share an identical physical winding waveform; difference is
    # ONLY reverse-port transfer fraction and charged control overhead.
    # ∆p=(∆eta)*max(-vi,0)-∆logic. The function max(-vi,0) inherits
    # |d(vi)/dx|<=Mcoil, which gives a rigorous Lipschitz quadrature bound.
    eta_delta=.99-.95
    gain_error=eta_delta*baseline['coil_abs_power_lipschitz_upper_w_per_rad']*math.pi/p.n
    return {'enhanced_same_waveform_gain_w':gain,
            'enhanced_same_waveform_gain_interval_w':[gain-gain_error,gain+gain_error],
            'enhanced_same_waveform_gain_certified_positive':gain>gain_error,
            'candidates':candidates,'sampled_feasible_count' :len(feasible),'continuous_winding_envelope_count':len(certified),'best_sampled':max(feasible,key=lambda r:r['net_bus_w']) if feasible else None,
            'best_with_conservative_winding_envelope':max(certified,key=lambda r:r['net_bus_w']) if certified else None,
            'baseline':baseline,'all_arms_model_not_v2':True,
            'finite_enumerated_optimal_only':True}


def flywheel_deficit(*,rpm:float=2354.,delta_w:float=45.,duration_s:float=1.,tolerance_fraction:float=.01,inertia_kgm2:float=.01)->dict:
    if not (rpm>0 and delta_w>=0 and duration_s>0 and 0<tolerance_fraction<1 and inertia_kgm2>0):raise ValueError('invalid storage assumption')
    omega=2*math.pi*rpm/60
    e=delta_w*duration_s
    # Allowed decay from initial omega to omega*(1-tolerance).
    unit_j=.5*omega**2*(1-(1-tolerance_fraction)**2)
    minimum_inertia=e/unit_j
    wfinal_sq=omega**2-2*e/inertia_kgm2
    wfinal=math.sqrt(max(0.,wfinal_sq))
    return {'required_energy_j':e,'maximum_rpm_drop_fraction':tolerance_fraction,'minimum_inertia_kgm2':minimum_inertia,
            'actual_inertia_kgm2':inertia_kgm2,'final_rpm_if_only_storage':rpm*wfinal/omega,
            'rotor_exhausted_before_duration':wfinal_sq<0,
            'interpretation':'Only kinetic storage supplying entire deficit, with no compensating shaft input'}


def loss_interval(*,load_added_w:float=45.,delta_input_interval_w=(-2.,2.),delta_aux_interval_w=(0.,0.),delta_storage_rate_interval_w=(0.,0.),delta_other_output_interval_w=(0.,0.))->dict:
    """Exact interval propagation of differential conservation equation.
    delta_loss=P_in+P_aux-P_load-d(storage)/dt-P_other.
    Negative delta_loss means loss suppression. Interval endpoints independent.
    """
    if load_added_w<0:raise ValueError('load must be added')
    ranges=[delta_input_interval_w,delta_aux_interval_w,delta_storage_rate_interval_w,delta_other_output_interval_w]
    if any(len(x)!=2 or x[0]>x[1] for x in ranges):raise ValueError('invalid interval')
    a,b,c,d=ranges
    lower=a[0]+b[0]-load_added_w-c[1]-d[1]
    upper=a[1]+b[1]-load_added_w-c[0]-d[0]
    return {'delta_loss_interval_w':[lower,upper], 'required_loss_suppression_interval_w':[-upper,-lower],
            'identifiability':'conditional bounds only; auxiliary/storage/other outputs must be measured or bounded'}


def observation_rank():
    """Linear observation matrix on unknown (delta aux, delta losses,
    delta E_dot, delta other outputs) if delta load and input observed.
    Equation delta load - delta input = aux - losses - E_dot - other.
    """
    A=np.array([[1.,-1.,-1.,-1.]])
    return {'unknowns':['delta_auxiliary_w','delta_losses_w','delta_storage_rate_w','delta_other_outputs_w'],
            'meter_equations_rank':int(np.linalg.matrix_rank(A)),
            'nullity':int(4-np.linalg.matrix_rank(A)),
            'minimal_extra_independent_constraints':3,
            'note':'Need three independent measured/bounded independent combinations to identify remaining scalar; choosing specific instruments is a physical design decision'}


def run():
    plant=Plant()
    g=frontier(plant)
    return {'schema':'dashi.V2.Omega.smooth-storage-identifiability.v1','source':'invented reversible saturating winding, not V2',
        'plant':asdict(plant),'frontier':g,'rotor_deficit_1s':flywheel_deficit(),
        'rotor_deficit_10s':flywheel_deficit(duration_s=10.),
        'meter_rank':observation_rank(),'loss_interval':loss_interval(),
        'original_v2_physical_identified':False,'agda_kernel_accepted':False}


if __name__=='__main__':
    r=run()
    out=Path(__file__).resolve().parents[1]/'Artifacts/v2_omega_smooth_storage_metrology_maxcut_20261116.json'
    out.parent.mkdir(exist_ok=True,parents=True)
    out.write_text(json.dumps(r,indent=2)+'\n')
    print(json.dumps({k:r['frontier'][k] for k in ('sampled_feasible_count','continuous_winding_envelope_count','baseline','best_sampled','best_with_conservative_winding_envelope')},indent=2))