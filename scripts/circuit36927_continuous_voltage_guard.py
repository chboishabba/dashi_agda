"""Conservative continuous-waveform guard for the DASHI steelman PM motor.

Uses Fourier interpolation and its angular derivative on 8x grid.
Additionally bounds *between-grid* maxima by an explicit Fourier
coefficient derivative bound. This is a mathematical interpolation model:
physical controller bandwidth/PWM ripple and magnetic geometry are not
certified. Floating-point certificate needs outward-rounded intervals for
a machine-checkable numerical proof. No original manufacturer wiring.
"""
from dataclasses import replace
import json
import numpy as np
from scipy.optimize import minimize
from scipy.signal import resample
from circuit36927_joint_voltage_constrained_drive import Motor, model, copper_reference, assess

def interpolation(n, factor):
    m=n*factor
    T=resample(np.eye(n),m,axis=0)
    freq=np.fft.fftfreq(m,d=1./m)
    D=np.fft.ifft(1j*freq[:,None]*np.fft.fft(T,axis=0),axis=0).real
    return T,D

def derivative_sup_bound(samples):
    """For Fourier polynomial f, sup|f'| <= sum |k fhat[k]|."""
    n=len(samples)
    k=np.fft.fftfreq(n,d=1./n)
    return float(sum(abs(k*np.fft.fft(samples)/n)))

def continuous_envelope(samples):
    """Nearest-grid bound, sup|f| <= max_sample|f| + pi/n*sup|f'|."""
    return float(max(abs(samples))+np.pi/len(samples)*derivative_sup_bound(samples))

def guarded_optimum(m=Motor(),n=81,factor=8,bipolar=False,
                    voltage_margin=0.,current_margin=0.):
    k,_,V,emf=model(m,n)
    T,D=interpolation(n,factor)
    F=m.R*T+m.L*m.speed*D
    fine_emf=m.speed*m.K*np.sin(2*np.pi*np.arange(n*factor)/(n*factor))
    reference=copper_reference(m,k,bipolar)
    Q=m.R*np.eye(n)/n
    lo=-m.imax if bipolar else 0.
    torquerow=k/n
    def inequalities(i):
        finei=T@i
        finev=F@i+fine_emf
        return np.r_[m.bus-voltage_margin-finev,
                     m.bus-voltage_margin+finev,
                     m.imax-current_margin-finei,
                     finei-lo-current_margin]
    J=np.vstack((-F,F,-T,T))
    fit=minimize(lambda i:float(i@Q@i),reference,
          jac=lambda i:2*Q@i,method="SLSQP",
          bounds=[(lo,m.imax)]*n,
          constraints=[dict(type="eq",
                  fun=lambda i:float(np.dot(torquerow,i)-m.torque),
                  jac=lambda i:torquerow),
                       dict(type="ineq",fun=inequalities,jac=lambda i:J)],
          options=dict(ftol=1e-10,maxiter=300))
    if not fit.success:raise RuntimeError(fit.message)
    finei=T@fit.x
    finev=F@fit.x+fine_emf
    vbound=continuous_envelope(finev)
    slope_i=derivative_sup_bound(finei)
    iboundlo=float(min(finei)-np.pi/len(finei)*slope_i)
    iboundhi=float(max(finei)+np.pi/len(finei)*slope_i)
    if vbound > m.bus+1e-6 or iboundlo<lo-1e-6 or iboundhi>m.imax+1e-6:
        raise ValueError("continuous-envelope certificate failed")
    fine_phase=2*np.pi*np.arange(len(finei))/len(finei)
    shaft=m.speed*float(np.mean(m.K*np.sin(fine_phase)*finei))
    copper=m.R*float(np.mean(finei**2))
    pin=float(np.mean(finei*finev))
    assert abs(pin-shaft-copper)<1e-8
    base=assess(m,fit.x,k,model(m,n)[1],V,emf)
    return dict(voltage_envelope_bound_v=vbound,
        current_envelope_lower_a=iboundlo,
        current_envelope_upper_a=iboundhi,
        fine_grid_peak_v=float(max(abs(finev))),
        shaft_w=shaft,copper_w=copper,bus_w=base["bus_w"],
        shaft_to_bus_efficiency=shaft/base["bus_w"],
        winding_power_balance_residual_w=pin-shaft-copper,
        iterations=int(fit.nit), 
        certificate_scope="selected bandlimited Fourier waveform; floating precision")

def test():
    cases={}
    for m in (Motor(),replace(Motor(),speed=250.,bus=12.)):
        for bipolar in (False,True):
            # Separate generous-margin 24V case from tight 12V case.
            voltage_margin=1.02 if m.bus==12. else 0.
            key=f"speed={m.speed}_bus={m.bus}_bipolar={bipolar}"
            cases[key]=guarded_optimum(m,81,8,bipolar,voltage_margin,.03)
    return dict(status="passed",cases=cases,
        physical_switching_or_motor_verified=False,
        interval_arithmetic_kernel_verified=False)

if __name__=="__main__":print(json.dumps(test(),indent=2))
