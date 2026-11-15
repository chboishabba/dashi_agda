#!/usr/bin/env python3
"""Independent synthetic reluctance-generator phase-count / pulse-recovery audit.

Not calibrated to @madscience369 V2, Slobodian MG10 or Holmstrom motors.
Linear magnetic coenergy; no saturation, hysteresis, permanent-magnet forcing,
mutual flux paths, semiconductor dead time or physical winding-design proof.
Uses pre-existing DASHI phase/MDL ideas as *donors*, not attributed origins.
"""
from __future__ import annotations
import json
import math
from dataclasses import asdict, dataclass, replace
from pathlib import Path
import numpy as np
from scipy.optimize import minimize
import sympy as sp

@dataclass(frozen=True)
class Model:
    rpm: float = 2354.0                  # reel speed, reused as scenario setting
    pole_harmonic: int = 4               # NOT measured in V2
    L_mean_h: float = 0.020             # illustrative
    L_cos_amplitude_h: float = 0.004    # illustrative; L>0
    R_ohm: float = 0.30                 # illustrative per channel
    total_mean_current_sq_a2: float = 35.0  # sum of phase RMS current^2, fixed
    bus_voltage_v: float = 250.0        # hypothetical bound
    eta_forward: float = 0.98           # drive efficiency
    eta_reverse: float = 0.98           # recovery efficiency
    switch_overhead_w_per_phase: float = 0.15  # hypothetical scaling
    samples: int = 3072

    @property
    def omega(self):
        return 2*math.pi*self.rpm/60


def coenergy_symbolic_certificate() -> dict:
    L0, a, omega, r = sp.symbols('L0 a omega R', real=True)
    t, k, beta = sp.symbols('t k beta', real=True)
    q, qd = sp.symbols('q qdot', real=True)
    theta = sp.symbols('theta', real=True)
    L = L0 + a*sp.cos(k*theta+beta)
    Lprime = sp.diff(L, theta)
    voltage = r*q + L*qd + omega*Lprime*q
    stored_derivative = L*q*qd + sp.Rational(1,2)*Lprime*omega*q*q
    torque = sp.Rational(1,2)*q*q*Lprime
    identity = sp.simplify(q*voltage-r*q*q-stored_derivative-torque*omega)
    assert identity == 0
    # Three-phase cancellation of equally spaced first-harmonic phasors,
    # and the higher-harmonic cancellation for m>=3.
    z = sp.exp(2*sp.pi*sp.I/3)
    phase_sum = sp.simplify(sp.expand_complex(1+z+z**2))
    assert phase_sum == 0
    # Inductance/permeance derivation under linear fixed magnetic geometry.
    N, P0, P1 = sp.symbols('N P0 P1', positive=True)
    permeance = P0 + P1*sp.cos(k*theta)
    inductance = N**2*permeance
    assert sp.simplify(sp.diff(inductance,theta)-N**2*sp.diff(permeance,theta))==0
    # Saturation extension: coenergy W'(i,theta)=integral_0^i lambda(s,theta) ds.
    # This is nonlinear (coenergy != 1/2 Li^2); differential inductance
    # positivity has to be enforced by a separate physical producer.
    b=sp.Function('b')(theta)
    Ltheta=sp.Function('L')(theta)
    flux=Ltheta*q-b*q**3
    coenergy=sp.Rational(1,2)*Ltheta*q**2-sp.Rational(1,4)*b*q**4
    stored=sp.expand(q*flux-coenergy)
    nonlinear_torque=sp.diff(coenergy,theta)
    nonlinear_port=r*q**2+q*(sp.diff(flux,q)*qd+sp.diff(flux,theta)*omega)
    nonlinear_res=sp.simplify(nonlinear_port-r*q**2-
       (sp.diff(stored,q)*qd+sp.diff(stored,theta)*omega)-nonlinear_torque*omega)
    assert nonlinear_res==0
    # Linear two-coil mutual inductance extension, symmetric L(theta).
    u,v,ud,vd=sp.symbols('u v ud vd',real=True)
    La,Lb,M=sp.Function('La')(theta),sp.Function('Lb')(theta),sp.Function('M')(theta)
    currents=sp.Matrix([u,v]); rates=sp.Matrix([ud,vd])
    matrix=sp.Matrix([[La,M],[M,Lb]])
    dmatrix=sp.diff(matrix,theta)
    volts=matrix*rates+omega*dmatrix*currents
    magnetic=(currents.T*matrix*currents)[0]/2
    mutual_torque=(currents.T*dmatrix*currents)[0]/2
    magnetic_rate=sp.diff(magnetic,u)*ud+sp.diff(magnetic,v)*vd+sp.diff(magnetic,theta)*omega
    mutual_res=sp.simplify((currents.T*volts)[0]-magnetic_rate-mutual_torque*omega)
    assert mutual_res==0
    L_test=np.array([[.018,.005],[.005,.022]])
    assert np.linalg.eigvalsh(L_test).min()>0
    return {'linear_electromechanical_port_identity':'symbolically zero',
            'three_phasor_sum':'exactly zero',
            'nonlinear_saturating_coenergy_port_identity':'symbolically zero',
            'symmetric_mutual_inductance_port_identity':'symbolically zero',
            'linear_inductance_permeance_derivative':'exactly equal',
            'scope':'symbolic linear magnetics, not saturation/real machine'}


def ideal_phase_cover(m: int) -> dict:
    if m<3: raise ValueError('m>=3 required for everywhere-positive ideal phase coverage')
    h=math.pi/m
    # g_m(phi)=max_j sin(phi-2*pi*j/m), from ideal commutation.
    # min g_m=cos(pi/m); mean g_m=sin(pi/m)/(pi/m).
    # mean 1/g_m=log(sec(pi/m)+tan(pi/m))/(pi/m).
    return {'phases':m, 'worst_sensitivity':math.cos(h),
            'mean_sensitivity':math.sin(h)/h,
            'constant_torque_current_sq_multiplier':math.log(1/math.cos(h)+math.tan(h))/h}


def ideal_phase_optimisations():
    phase_data=[ideal_phase_cover(m) for m in range(3,13)]
    # equal dimensionless baseline copper coefficient; varying MDL/switch
    # penalty explicitly shows why no universal 369 optimum follows.
    case_weights=[0.005,0.010,0.015,0.020,0.030,0.050,0.150]
    winners={}
    for w in case_weights:
        sorted_costs=sorted((z['constant_torque_current_sq_multiplier']+w*z['phases'],z['phases']) for z in phase_data)
        winners[f'{w:.3f}']={'phase_count':sorted_costs[0][1], 'objective':sorted_costs[0][0]}
    # Independent grid vs closed form check of both max and inverse mean.
    phi=np.linspace(0,2*math.pi,300000,endpoint=False)
    for z in phase_data:
        m=z['phases']
        g=np.max(np.sin(phi[:,None]-2*np.pi*np.arange(m)[None,:]/m),axis=1)
        assert abs(g.min()-z['worst_sensitivity'])<0.00006, (m,g.min())
        assert abs(g.mean()-z['mean_sensitivity'])<1e-9, (m,g.mean())
        assert abs(np.mean(1/g)-z['constant_torque_current_sq_multiplier'])<1e-9, m
    return {'model':'ideal independent sinusoidal phases; perfect instantaneous switching',
            'phase_cover':phase_data,'cost_objective':'mean(1/g_m)+phase_overhead_weight*m',
            'winners':winners}


def simulate(m: int, phase_shift_rad: float, pulse_exponent: float, model: Model) -> dict:
    if not (3<=m<=12 and 1.5<=pulse_exponent<=4 and abs(phase_shift_rad)<=math.pi/3):
        raise ValueError('invalid scan point')
    if not model.L_mean_h > abs(model.L_cos_amplitude_h):
        raise ValueError('positive inductance required')
    theta=np.linspace(0,2*math.pi,model.samples,endpoint=False)
    ph=model.pole_harmonic*theta[:,None]-2*np.pi*np.arange(m)[None,:]/m
    sinp=np.sin(ph+phase_shift_rad)
    active=sinp>0
    u=np.maximum(sinp,0)
    # Normalise to identical sum of total RMS phase current² at all m.
    norm2=float(np.mean(np.sum(u**(2*pulse_exponent),axis=1)))
    I=math.sqrt(model.total_mean_current_sq_a2/norm2)
    current=I*u**pulse_exponent
    didt=I*pulse_exponent*np.where(active,u**(pulse_exponent-1)*np.cos(ph+phase_shift_rad),0)*model.omega*model.pole_harmonic
    L=model.L_mean_h+model.L_cos_amplitude_h*np.cos(ph)
    dLdtheta=-model.L_cos_amplitude_h*model.pole_harmonic*np.sin(ph)
    tau=0.5*np.sum(current**2*dLdtheta,axis=1)
    v=model.R_ohm*current+L*didt+current*model.omega*dLdtheta
    electrical_port_power=current*v
    magnetic_stored=0.5*np.sum(L*current**2,axis=1)
    magnetic_stored_rate=np.sum(L*current*didt+0.5*current**2*dLdtheta*model.omega,axis=1)
    copper_power=model.R_ohm*np.sum(current**2,axis=1)
    residual=electrical_port_power.sum(axis=1)-copper_power-magnetic_stored_rate-tau*model.omega
    assert float(np.max(np.abs(residual))) < 1e-8
    Pshaft=float(-np.mean(tau*model.omega))
    Pcopper=float(np.mean(copper_power))
    Pport=float(np.mean(electrical_port_power.sum(axis=1)))
    assert abs(Pport+Pshaft-Pcopper)<1e-4
    assert abs(float(np.mean(magnetic_stored_rate)))<1e-4
    source=float(np.mean(np.maximum(electrical_port_power,0).sum(axis=1)))
    recovery=float(np.mean(np.maximum(-electrical_port_power,0).sum(axis=1)))
    assert abs(Pport-source+recovery)<1e-9
    switch_loss=model.switch_overhead_w_per_phase*m
    Pbus=model.eta_reverse*recovery-source/model.eta_forward-switch_loss
    ripple_rms=float(np.std(tau)/abs(np.mean(tau))) if np.mean(tau)!=0 else float('inf')
    return {'phases':m,'phase_shift_rad':float(phase_shift_rad),'pulse_exponent':float(pulse_exponent),
            'mean_electromagnetic_braking_w':Pshaft,'copper_w':Pcopper,
            'ideal_net_electrical_out_w':-Pport,'realistic_bus_out_w':float(Pbus),
            'positive_coil_port_gross_w':source,'negative_coil_port_gross_w':recovery,
            'switch_overhead_w':switch_loss,'current_peak_per_phase_a':float(I),
            'peak_terminal_voltage_v':float(np.max(abs(v))),
            'mean_magnetic_storage_j':float(np.mean(magnetic_stored)),
            'max_sample_port_residual_w':float(np.max(abs(residual))),
            'mean_storage_derivative_w':float(np.mean(magnetic_stored_rate)),
            'torque_ripple_rms_over_mean':ripple_rms}


def optimize_pulses(model:Model):
    choices=[]
    for m in range(3,13):
        # SLSQP with a smooth periodic 3072-point synthetic waveform. Multiple
        # starts; no claim of globally optimal arbitrary switching control.
        def score(x):
            try:
                r=simulate(m,float(x[0]),float(x[1]),model)
                return -r['realistic_bus_out_w']
            except Exception:
                return 1e9
        def voltage_margin(x):
            return model.bus_voltage_v-simulate(m,float(x[0]),float(x[1]),model)['peak_terminal_voltage_v']
        starts=[(0.,1.5),(0.,2.),(0.25,1.5),(-0.25,1.5)]
        trials=[]
        for x0 in starts:
            r=minimize(score,x0,method='SLSQP',bounds=[(-0.7,0.7),(1.5,3.5)],
                constraints=[{'type':'ineq','fun':voltage_margin}],
                options={'maxiter':60,'ftol':1e-8})
            if voltage_margin(r.x)>-1e-4:
                trials.append(simulate(m,float(r.x[0]),float(r.x[1]),model))
        if not trials: raise RuntimeError(f'no feasible synthetic pulse for {m} phases')
        chosen=max(trials,key=lambda x:x['realistic_bus_out_w'])
        assert chosen['peak_terminal_voltage_v']<=model.bus_voltage_v+1e-4
        # Recheck 8x denser than the optimiser's angular samples. A dense
        # sample is still NOT an interval/Lipschitz certified continuous guard.
        guard=simulate(m,chosen['phase_shift_rad'],chosen['pulse_exponent'],
            replace(model,samples=model.samples*8))
        chosen['voltage_8x_peak_v']=guard['peak_terminal_voltage_v']
        chosen['high_resolution_voltage_pass']=guard['peak_terminal_voltage_v'] <= model.bus_voltage_v
        chosen['guard_type']='8x angular resampling; no continuous-interval proof'
        assert chosen['high_resolution_voltage_pass']
        chosen['8x_power_difference_w']=guard['realistic_bus_out_w']-chosen['realistic_bus_out_w']
        assert abs(chosen['8x_power_difference_w']) < 0.001
        choices.append(chosen)
    return {'model':'synthetic voltage-constrained family i_k=I*[sin(n*theta-2pi*k/m+delta)]_+^p',
            'objective':'max mean electrical bus export subject to fixed total RMS current^2, phase count, voltage cap',
            'best_over_all_m':max(choices,key=lambda x:x['realistic_bus_out_w']),
            'per_phase_count':choices,
            'limitations':'local multi-start SLSQP over delta,p; neither global control nor real hardware optimum'}


def run():
    model=Model()
    sym=coenergy_symbolic_certificate()
    ideal=ideal_phase_optimisations()
    # Negative-control synthetic energy conservation: ideal recovery still has copper losses.
    reference=[simulate(m,0,1.5,model) for m in (3,4,5,6,9)]
    for row in reference:
        assert row['ideal_net_electrical_out_w'] < row['mean_electromagnetic_braking_w']
        assert row['realistic_bus_out_w'] < row['ideal_net_electrical_out_w']
        assert abs(row['copper_w']-model.R_ohm*model.total_mean_current_sq_a2)<1e-8
    pulses=optimize_pulses(model)
    out={'schema':'dashi.generator.reluctance-phase-maxcut.v1',
         'attribution':{'v2_reel':'madscience369, 2026-11-14 transcript supplied by user',
                        'v2_direct_evidence':'2353-2354 RPM; input display 285-287 W; speaker reports ~45 W output',
                        'not_attributed_to_v2':'phase count, L, R, pole pairs, permeance, pulse timing, converter, storage or topology',
                        'distinct_sources':'Slobodian/Infinity SAV MG10 and Holmstrom/Resonate369 are separate designs',
                        'formal_reuse':'Tesla-compatible DASHI polyphase, circuit36927 recovery, KSW signed Poynting'},
         'not_a_device_calibration':True,'model_parameters':asdict(model),
         'symbolic':sym,'ideal_phase_cover':ideal,'sampled_waveforms':reference,
         'optimised_pulse_family':pulses}
    return out

if __name__=='__main__':
    out=run()
    path=Path(__file__).resolve().parents[1]/'Artifacts/v2_reluctance_phase_maxcut_receipt.json'
    path.parent.mkdir(parents=True,exist_ok=True)
    path.write_text(json.dumps(out,indent=2)+'\n')
    print(json.dumps({'symbolic':out['symbolic'],
        'ideal_optima':out['ideal_phase_cover']['winners'],
        'best_waveform':out['optimised_pulse_family']['best_over_all_m'],
        'receipt':str(path)},indent=2))