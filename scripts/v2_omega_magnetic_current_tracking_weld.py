#!/usr/bin/env python3
"""Continuous-voltage exact nonlinear two-winding current tracking weld.

Physically restricted: modeled L(theta), saturating lambda, passive memory z,
and motor rotor speed. No PWM dead-time or original V2 measurements.

For lambda(theta,i,z)=L(theta)i-beta*i^3+k*z, H=d lambda/di,
  v=R*i+lambda_theta*omega+k*z_dot+H*(r_theta*omega+gain*(r-i))
implies dot(i-r)=-gain*(i-r) exactly when voltage is unsaturated and H>0.
This is an exact continuous-time identity, not a numerical approximation.
"""
from dataclasses import dataclass,asdict
from pathlib import Path
import json,math
import numpy as np
from v2_omega_coupled_magnetic_torque import Model
from v2_omega_nonlinear_memory_torque import Memory,match_output,periodic_state
from v2_omega_finite_inertia_drive import Drive,comparison

@dataclass(frozen=True)
class Tracking:
    gain_hz:float=2500.0
    initial_error_bound_a:float=0.025
    speed_deviation_rpm:float=1.0
    memory_error_bound_a:float=0.026
    def validate(self):
        if self.gain_hz<=0 or self.initial_error_bound_a<0 or self.speed_deviation_rpm<0 or self.memory_error_bound_a<0:
            raise ValueError('invalid current tracking tube')

def maps(theta,i,z,m=Model(),mem=Memory()):
    L,A,B,R,c=m.arrays(); k,tau=mem.check()
    x=m.poles*theta;sn,cs=math.sin(x),math.cos(x)
    l=L+cs*A+sn*B; lx=m.poles*(-sn*A+cs*B)
    H=l-3*m.beta*np.diag(i*i)
    return l,lx,H,R,k,tau

def reference(theta,m,u,v):
    x=m.poles*theta
    c=m.arrays()[4]
    return c+math.sin(x)*u+math.cos(x)*v, m.poles*(math.cos(x)*u-math.sin(x)*v)

def controlled_step(theta,omega,i,z,u,v,tracking=Tracking(),m=Model(),mem=Memory()):
    tracking.validate()
    i=np.asarray(i,float); z=np.asarray(z,float)
    u=np.asarray(u,float);v=np.asarray(v,float)
    r,dr=reference(theta,m,u,v)
    l,lx,H,R,k,tau=maps(theta,i,z,m,mem)
    zdot=(i-z)/tau
    desired=dr*omega+tracking.gain_hz*(r-i)
    voltage=R*i+lx@i*omega+k*zdot+H@desired
    actual=np.linalg.solve(H,voltage-R*i-lx@i*omega-k*zdot)
    return {'v':voltage,'actual_di':actual,'reference_di':dr*omega,
            'error_derivative':actual-dr*omega,'error':i-r,'min_incremental_h':float(np.linalg.eigvalsh(H)[0]),
            'voltage_ok':float(np.max(abs(voltage)))<=m.voltage_limit}

def global_certificate(m=Model(),mem=Memory(),control=None,tracking=Tracking()):
    """Conservative all-angle tube bound, works for every |omega-omega0|<=dw.

    Assumes |i-r|_infty<=eps, |z-z_periodic|_infty<=z_eps.
    All separate terms are bounded using spectral norms, not sampled maxima.
    A bound exceeding limit is inconclusive (not proof of violation).
    """
    tracking.validate(); L,A,B,R,c=m.arrays();k,tau=mem.check()
    if control is None:control=match_output(m,mem,20.,True)
    u=np.array(control['u']);v=np.array(control['v'])
    _,U,V=periodic_state(m,mem,u,v)
    eps=tracking.initial_error_bound_a
    iz=np.abs(c)+np.abs(u)+np.abs(v)+eps
    zz=np.abs(c)+np.abs(U)+np.abs(V)+tracking.memory_error_bound_a
    dref=m.poles*(np.abs(u)+np.abs(v))
    w=m.omega+tracking.speed_deviation_rpm*2*math.pi/60
    lp=m.poles*(np.linalg.norm(A,2)+np.linalg.norm(B,2))
    lm=np.linalg.norm(L,2)+np.linalg.norm(A,2)+np.linalg.norm(B,2)
    # Reuse the proven all-angle *nominal* winding bound from the same magnetic
    # producer. Then bound only perturbations (triangle inequalities), preventing
    # an unrelated gross norm bound from obscuring the narrow tracking tube.
    from v2_omega_nonlinear_memory_torque import periodic_ledger
    nominal=periodic_ledger(m,mem,u,v)['sufficient_voltage_upper_bound_v']
    dw=tracking.speed_deviation_rpm*2*math.pi/60
    rmax=np.abs(c)+np.abs(u)+np.abs(v)
    rprime=m.poles*(np.abs(u)+np.abs(v))
    nr=float(np.linalg.norm(rmax)); nd=float(np.linalg.norm(rprime))
    inorm=math.sqrt(2)*eps
    Hnorm=lm+3*m.beta*np.max(iz)**2
    perturb=(float(np.max(R))*eps + lp*inorm*w +
        3*m.beta*(2*np.max(rmax)*eps+eps*eps)*nd*w +
        Hnorm*tracking.gain_hz*inorm +
        float(np.max(k/tau))*(eps+tracking.memory_error_bound_a) +
        (lp*nr+Hnorm*nd)*dw)
    bound=float(nominal+perturb)
    # Magnetic lag error relative to the *nominal-speed* periodic angle profile obeys
    # dz_error/dt=(current_error-z_error)/tau - z_reference_theta*delta_omega.
    # A sufficient invariant lag tube is z_eps >= eps + tau*|zref_theta|*|delta_omega|.
    mem_required=float(np.max(eps+tau*m.poles*(np.abs(U)+np.abs(V))*dw))
    # This bound is intentionally conservative; a failure of the upper bound is not a physical rejection.
    eig_margin=float(np.linalg.eigvalsh(L).min()-np.linalg.norm(A,2)-np.linalg.norm(B,2)-3*m.beta*np.max(iz)**2)
    return {'sufficient_voltage_bound_v':bound,'limit_v':m.voltage_limit,'voltage_certified':bound<=m.voltage_limit,
        'min_incremental_inductance_bound_h':eig_margin,'invertibility_certified':eig_margin>0,
        'sufficient_peak_current_a':float(np.max(iz)),'current_certified':float(np.max(iz))<=m.current_limit,
        'speed_tube_rpm':tracking.speed_deviation_rpm,'current_initial_error_bound_a':eps,
        'gain_hz':tracking.gain_hz,'memory_tube_bound_a':tracking.memory_error_bound_a,
        'memory_tube_invariant_sufficient':tracking.memory_error_bound_a>=mem_required,
        'memory_tube_required_a':mem_required}

def sampled_certificate(m=Model(),mem=Memory(),control=None,tracking=Tracking(),n=512):
    """Diagnostic samples, not a continuous all-angle or PWM certificate."""
    if control is None:control=match_output(m,mem,20.,True)
    u=np.asarray(control['u']);v=np.asarray(control['v']);_,U,V=periodic_state(m,mem,u,v)
    maxv=0.;mineig=math.inf
    for th in np.linspace(0,2*math.pi/m.poles,n,endpoint=False):
        r,dr=reference(th,m,u,v); x=m.poles*th
        z=m.arrays()[4]+math.sin(x)*U+math.cos(x)*V
        data=controlled_step(th,m.omega,r,z,u,v,tracking,m,mem)
        maxv=max(maxv,float(np.max(abs(data['v']))))
        mineig=min(mineig,data['min_incremental_h'])
    return {'sampled_max_voltage_v':maxv,'sampled_min_incremental_h':mineig}

def experiment():
    m=Model();mem=Memory(); results={}
    for aware in (True,False):
        key='memory_aware' if aware else 'copper_only'
        ctrl=match_output(m,mem,20.,aware)
        # Exact invariant manifold e=0 requires no tracking error, so feedforward needs only
        # global_certificate with epsilon=0; memory is periodic along the prescribed waveform.
        nominal=Tracking(initial_error_bound_a=0.,memory_error_bound_a=0.)
        nearby=Tracking(initial_error_bound_a=.025,memory_error_bound_a=.026)
        results[key]={'nominal_exact_reference':global_certificate(m,mem,ctrl,nominal),
            'tracking_tube':global_certificate(m,mem,ctrl,nearby),
            'sampled_diagnostic':sampled_certificate(m,mem,ctrl)}
    return {'schema':'DASHI.V2.magnetic-tracking-conditional.v1','controller_identity':'di_dt - dr_dt = -gain*(i-r), when unsaturated and Hessian invertible',
        'modelled_targets':results,
        'open_gates':['closed-loop coupled rotor periodic-orbit theorem','real switched PWM tracking','hardware voltage transients','motor torque sufficiency for original V2','source-selected material and thermal map'],
        'scope':'hypothetical continuous voltage actuator, fixed recovery, no original V2 measurements'}

def full_receipt():
    record=experiment()
    record['coupled_numerical']={'memory_aware':execute_coupled(aware=True),'copper_only':execute_coupled(aware=False)}
    return record


def execute_coupled(drive=Drive(turns=12),tracking=Tracking(),aware=True,initial_error_a=0.025):
    """Simultaneously integrate theta, omega, actual winding i, magnetic lag z.

    This is a *numerical* same-system weld; no validated interval error or
    periodic orbit. The continuous controller is voltage clipped per winding,
    and a clipped run is NOT certified by the exact tracking-error theorem.
    """
    from scipy.integrate import solve_ivp
    drive.validate();tracking.validate()
    m=Model();mem=Memory();L,A,B,R,c=m.arrays();k,tau=mem.check()
    q=match_output(m,mem,20.,aware)
    u=np.array(q['u']);v=np.array(q['v']);_,U,V=periodic_state(m,mem,u,v)
    r0,_=reference(0.,m,u,v)
    z0=c+V
    ff=q['shaft_w']/m.omega+drive.viscous_nm_per_rad_s*m.omega
    # theta, omega, i[2], z[2], motor W, copper W, memory W,
    # electrical export W, friction W, clipping and torque saturation durations
    y0=[0.,m.omega,*(r0+np.array([initial_error_a,-initial_error_a])),*z0,0.,0.,0.,0.,0.,0.,0.]
    def evaluation(y):
        theta,omega=y[:2];i=y[2:4];z=y[4:6]
        r,dr=reference(theta,m,u,v)
        l,lx,H,R,k,tau=maps(theta,i,z,m,mem)
        zdot=(i-z)/tau
        vcmd=R*i+lx@i*omega+k*zdot+H@(dr*omega+tracking.gain_hz*(r-i))
        vreal=np.clip(vcmd,-m.voltage_limit,m.voltage_limit)
        didt=np.linalg.solve(H,vreal-R*i-lx@i*omega-k*zdot)
        torque=float(.5*i@lx@i)
        motor_raw=ff+drive.proportional_nm_per_rad_s*(m.omega-omega)
        tm=float(np.clip(motor_raw,-drive.torque_max_nm,drive.torque_max_nm))
        friction=drive.viscous_nm_per_rad_s*omega
        return r,zdot,vcmd,vreal,didt,torque,tm,friction,float(np.max(abs(vcmd))>m.voltage_limit),float(abs(motor_raw)>drive.torque_max_nm)
    def rhs(t,y):
        theta,omega=y[:2];i=y[2:4];z=y[4:6]
        r,zdot,vcmd,vreal,didt,torque,tm,friction,clip,sat=evaluation(y)
        dw=(tm+torque-friction)/drive.inertia_kgm2
        return [omega,dw,*didt,*zdot,tm*omega,float(R@(i*i)),float(np.dot(k/tau,(i-z)**2)),
                -float(i@vreal),friction*omega,clip,sat]
    end=drive.turns*2*math.pi/m.omega*1.015
    sol=solve_ivp(rhs,(0,end),y0,method='LSODA',rtol=2e-8,atol=1e-10,max_step=drive.max_step_s,dense_output=True)
    if not sol.success:raise RuntimeError(sol.message)
    tgrid=np.linspace(0,end,5000);ths=sol.sol(tgrid)[0]
    if np.any(np.diff(ths)<=0):raise ValueError('rotor reverse invalidates cycles')
    angles=np.array([drive.turns-1,drive.turns])*2*math.pi
    times=np.interp(angles,ths,tgrid)
    a,b=np.asarray(sol.sol(times)).T
    duration=times[1]-times[0]
    # Use exact stored energy from the same two-winding co-energy.
    def Emag(y):
        theta=y[0];i=y[2:4];z=y[4:6]
        l=maps(theta,i,z,m,mem)[0]
        return float(.5*i@l@i-.75*m.beta*np.sum(i**4)+.5*np.dot(k,z*z))
    drot=.5*drive.inertia_kgm2*(b[1]**2-a[1]**2)
    dmag=Emag(b)-Emag(a)
    motor=(b[6]-a[6]);copper=(b[7]-a[7]);memory=(b[8]-a[8]);export=(b[9]-a[9]);friction=(b[10]-a[10])
    residual=motor-export-copper-memory-friction-drot-dmag
    sample=np.asarray(sol.sol(np.linspace(times[0],times[1],600)))
    voltages=[];errors=[];reaction=[];speed=[]
    for y in sample.T:
        r,zdt,cmd,vreal,di,torque,tm,fric,clip,sat=evaluation(y)
        voltages.append(float(np.max(abs(cmd))));errors.append(float(np.max(abs(y[2:4]-r))))
        reaction.append(abs(torque));speed.append(y[1])
    return {'schema':'DASHI.V2.coupled-drive-current-tracking.numerical.v1',
       'aware':aware,'last_cycle_drive_w':motor/duration,'last_cycle_export_bus_w':m.bus_eta*export/duration,
       'copper_w':copper/duration,'memory_w':memory/duration,'friction_w':friction/duration,
       'rotor_storage_rate_w':drot/duration,'magnetic_storage_rate_w':dmag/duration,
       'balance_residual_j':residual,'peak_command_voltage_v':max(voltages),
       'peak_current_error_a':max(errors), 'peak_abs_reaction_nm':max(reaction),
       'max_speed_deviation_rpm':max(abs(np.array(speed)-m.omega))*60/(2*math.pi),
       'voltage_clipped_fraction':(b[11]-a[11])/duration,'torque_saturated_fraction':(b[12]-a[12])/duration,
       'last_cycle_duration_s':duration,
       'status':'numerical trajectory, not rigorously certified periodic orbit or switched PWM'}

if __name__=='__main__':print(json.dumps(full_receipt(),indent=2,default=lambda x:x.item() if hasattr(x,'item') else str(x)))
