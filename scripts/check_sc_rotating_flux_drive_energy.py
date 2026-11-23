#!/usr/bin/env python3
"""Physical rotating-flux pump power, no anomalous gravity coefficient.

Finite RL induction surrogate, mathematical integration of Filsinger signed
source/driver work; not a full YBCO vortex/critical-state FEM.
Separate RF pump phase omega_d t and mechanical p theta.
"""
import sympy as s
def check():
    i,L,R,Omega,wd,p,Phi0,psi=s.symbols("i L R Omega wd p Phi0 psi",real=True)
    flux_theta=-p*Phi0*s.sin(psi)
    flux_t=wd*Phi0*s.sin(psi)
    assert s.simplify(flux_theta*Omega+flux_t-
                      Phi0*s.sin(psi)*(wd-p*Omega))==0
    di=-(R*i+flux_theta*Omega+flux_t)/L
    U_dot=L*i*di
    mech_power=-i*flux_theta*Omega
    pump_power=-i*flux_t
    assert s.simplify(U_dot+R*i**2-mech_power-pump_power)==0
    assert 3_500_000/(5000/60)>40000
    print("PASS exact energy: d(Li²/2)/dt +Ri² = P_mechanical + P_RF_pump")
    print("3.5MHz / (5000rpm mechanical Hz) =",3_500_000/(5000/60))
    print("Thus MHz AC is not automatically mechanical frequency matching.")
    print("Needs measured L,R, torque/phase/current, critical pinning and flux history.")
if __name__=="__main__":check()
