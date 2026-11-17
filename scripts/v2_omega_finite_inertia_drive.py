#!/usr/bin/env python3
"""Finite-inertia, torque-limited motor weld for hypothetical magnetic-memory V2.

Extends the SAME existing two-winding coenergy/current programmes; NO changes to
recovery efficiency or magnetic geometry. Uses angular current tracking as an
*imposed* current waveform (not a proven voltage/PWM current controller).
Tracks independent magnetic and rotor energy plus mechanical and electrical
ports with integrator states. Numbers are not original V2 measurements.
"""
from dataclasses import dataclass, asdict
import json, math
import numpy as np
from scipy.integrate import solve_ivp
from v2_omega_coupled_magnetic_torque import Model
from v2_omega_nonlinear_memory_torque import Memory, match_output, periodic_state

@dataclass(frozen=True)
class Drive:
    inertia_kgm2:float=.02
    torque_max_nm:float=.65
    viscous_nm_per_rad_s:float=0.00006
    proportional_nm_per_rad_s:float=.22
    integral_nm_per_rad:float=0.0
    turns:int=30
    max_step_s:float=.0004
    def validate(self):
        if min(self.inertia_kgm2,self.torque_max_nm,self.proportional_nm_per_rad_s,self.max_step_s)<=0 or self.viscous_nm_per_rad_s<0 or self.turns<4:
            raise ValueError('invalid motor-drive parameters')

def fields(theta,omega,z,m,mem,u,v):
    L,A,B,R,c=m.arrays();k,tau=mem.check();u=np.asarray(u);v=np.asarray(v)
    x=m.poles*theta;sn,cs=math.sin(x),math.cos(x)
    i=c+sn*u+cs*v
    ix=cs*u-sn*v
    La=L+cs*A+sn*B
    Lx=-sn*A+cs*B
    zdot=(i-z)/tau
    lam=La@i-m.beta*i**3+k*z
    lamdot=m.poles*omega*(Lx@i+La@ix-3*m.beta*i*i*ix)+k*zdot
    volt=R*i+lamdot
    torque=.5*m.poles*i@Lx@i  # signed torque ON rotor
    copper=R@(i*i)
    memory=np.dot(k/tau,(i-z)**2)
    Emag=.5*i@La@i-.75*m.beta*sum(i**4)+.5*k@(z*z)
    terminal=i@volt
    # signed electrical power INTO coil; exported electric power = -terminal
    return dict(i=i,z=z,zdot=zdot,voltage=volt,torque=torque,copper=copper,memory=memory,Emag=Emag,terminal=terminal,
                export_raw=-terminal)

def execute(m=Model(),mem=Memory(),drive=Drive(),aware=True,target=20.):
    drive.validate();m.arrays();mem.check()
    control=match_output(m,mem,target,aware)
    u=np.array(control['u']);v=np.array(control['v'])
    c,U,V=periodic_state(m,mem,u,v)
    z0=c+V
    initial=fields(0,m.omega,z0,m,mem,u,v)
    ff=control['shaft_w']/m.omega+drive.viscous_nm_per_rad_s*m.omega
    # theta, omega, z1,z2, controller-integral, integrals of drive work,
    # copper, memory, raw export, friction loss, drive torque saturation time,
    # and positive torque work (for diagnostics).
    y0=np.array([0.,m.omega,*z0,0.,0.,0.,0.,0.,0.,0.,0.])
    def rhs(t,y):
        theta,omega=y[:2];z=y[2:4]
        f=fields(theta,omega,z,m,mem,u,v)
        raw=ff+drive.proportional_nm_per_rad_s*(m.omega-omega)+drive.integral_nm_per_rad*y[4]
        tm=float(np.clip(raw,-drive.torque_max_nm,drive.torque_max_nm))
        friction=drive.viscous_nm_per_rad_s*omega
        dw=(tm+f['torque']-friction)/drive.inertia_kgm2
        return [omega,dw,*f['zdot'],m.omega-omega,
                tm*omega,f['copper'],f['memory'],f['export_raw'],friction*omega,
                float(abs(raw)>drive.torque_max_nm),tm*omega if tm>0 else 0.]
    period=2*math.pi/m.omega
    end=drive.turns*period*1.01
    sol=solve_ivp(rhs,(0,end),y0,method='LSODA',rtol=2e-8,atol=1e-10,max_step=drive.max_step_s,dense_output=True)
    if not sol.success:raise RuntimeError(sol.message)
    # compare integral ledgers at EXACT angular cycle boundaries, not timer intervals
    tgrid=np.linspace(0,end,4000)
    th=sol.sol(tgrid)[0]
    if np.any(np.diff(th)<=0):raise RuntimeError('rotor reversed; angle-cycle analysis invalid')
    angles=np.arange(drive.turns+1)*2*math.pi
    times=np.interp(angles,th,tgrid)
    rows=np.asarray(sol.sol(times)).T
    def cycle(start,stop):
        a,b=rows[start],rows[stop]
        d=b-a;duration=times[stop]-times[start]
        Em0=fields(a[0],a[1],a[2:4],m,mem,u,v)['Emag']
        Em1=fields(b[0],b[1],b[2:4],m,mem,u,v)['Emag']
        dErot=.5*drive.inertia_kgm2*(b[1]**2-a[1]**2)
        dEmag=Em1-Em0
        work_motor=d[5];work_export=d[8];work_cu=d[6];work_mem=d[7];work_fric=d[9]
        residual=work_motor-work_export-work_cu-work_mem-work_fric-dErot-dEmag
        return dict(duration_s=duration,drive_w=work_motor/duration,export_raw_w=work_export/duration,
                    export_bus_signed_ideal_w=m.bus_eta*work_export/duration,
                    copper_w=work_cu/duration,memory_w=work_mem/duration,
                    friction_w=work_fric/duration,rotor_storage_rate_w=dErot/duration,
                    magnetic_storage_rate_w=dEmag/duration,
                    balance_residual_j=residual,omega_first=a[1],omega_last=b[1],
                    saturation_fraction=d[10]/duration)
    last=cycle(drive.turns-1,drive.turns)
    preceding=cycle(drive.turns-2,drive.turns-1)
    # selected fixed angular grid in final cycle, for peak torque/voltage tracking
    theta_samples=np.linspace(2*math.pi*(drive.turns-1),2*math.pi*drive.turns,513)
    ts=np.interp(theta_samples,th,tgrid)
    ys=sol.sol(ts)
    diagnostics=[fields(ys[0,j],ys[1,j],ys[2:4,j],m,mem,u,v) for j in range(len(ts))]
    vpk=max(float(np.max(np.abs(q['voltage']))) for q in diagnostics)
    ipk=max(float(np.max(np.abs(q['i']))) for q in diagnostics)
    reactionpk=max(abs(q['torque']) for q in diagnostics)
    motor_torques=np.clip(ff+drive.proportional_nm_per_rad_s*(m.omega-ys[1])+drive.integral_nm_per_rad*ys[4],-drive.torque_max_nm,drive.torque_max_nm)
    motor_torque_peak=float(np.max(np.abs(motor_torques)))
    # Samples check tracking, but do not certify switching or the continuous peak.
    speed_error_rpm=float(np.max(np.abs(ys[1]-m.omega))*60/(2*math.pi))
    result=dict(schema='DASHI.V2.finite-inertia-magnetic-memory.v1',awareness=aware,
       parameters=asdict(drive),original_material_assumed=True,target_at_fixed_speed_w=target,
       cycle=last,prior_cycle=preceding,
       last_cycle_deviation_w=abs(last['drive_w']-preceding['drive_w']),
       peak_reaction_torque_nm=reactionpk,peak_motor_torque_nm=motor_torque_peak,peak_speed_error_rpm=speed_error_rpm,peak_current_a=ipk,peak_sampled_voltage_v=vpk,
       sampled_voltage_feasible=vpk<=m.voltage_limit,
       sampled_current_feasible=ipk<=m.current_limit,
       terminal_speed_rpm=rows[-1,1]*60/(2*math.pi),
       last_cycle_speed_variation_rpm=(max(ys[1])-min(ys[1]))*60/(2*math.pi),
       pointwise_periodic_memory_stored_estimate_j=initial['Emag'],
       numerically_steady_last_cycle=(abs(last['rotor_storage_rate_w'])<.005 and abs(last['magnetic_storage_rate_w'])<.25 and abs(last['balance_residual_j'])<.0001 and last['saturation_fraction']<.001),
       acceptance='model numerical integration only; no PWM, switching, temperature or original V2 calibration')
    return result

def comparison(drive=Drive()):
    a=execute(drive=drive,aware=True)
    b=execute(drive=drive,aware=False)
    return dict(memory_aware=a,copper_only=b,
      actual_dynamic_bus_delta_w=a['cycle']['export_bus_signed_ideal_w']-b['cycle']['export_bus_signed_ideal_w'],
      actual_dynamic_drive_delta_w=b['cycle']['drive_w']-a['cycle']['drive_w'],
      shaft_saving_steady_target_w=(match_output(Model(),Memory(),20.,False)['shaft_w']-match_output(Model(),Memory(),20.,True)['shaft_w']),
      note='When controls are matched at fixed speed, varying-speed outputs may not be exactly matched; do not infer equal-output saving without rematching.')

if __name__=='__main__':print(json.dumps(comparison(),indent=2,default=lambda x:x.item() if hasattr(x,'item') else str(x)))
