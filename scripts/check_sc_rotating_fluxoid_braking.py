#!/usr/bin/env python3
"""Conditional London fluxoid-ring braking: quantized current, exact work.

Original underlying physics: superconducting fluxoid quantization, rotating
superconducting London moment. Filsinger signed material/source ports reused.
User-origin coherent charged matter braking steelman; current finite-loop
model is new mathematical synthesis, not a full spatial YBCO TDGL or gravity.
Fixed winding number n except an independently paid phase-slip event.
"""
import sympy as s

def main():
    Lk,Lg,A,m,q,Om,Ph,Phx,Ph0,n=s.symbols(
        'L_k L_g A m q Omega Phi Phi_ext Phi_0 n',real=True,nonzero=True)
    f=n*Ph0-2*m*A*Om/q
    I=(f-Ph)/Lk
    U=s.factor((f-Ph)**2/(2*Lk)+(Ph-Phx)**2/(2*Lg))
    Ph_eq=s.solve(s.diff(U,Ph),Ph)[0]
    assert s.simplify(Ph_eq-(Lg*f+Lk*Phx)/(Lg+Lk))==0
    assert s.simplify(I.subs(Ph,Ph_eq)-(f-Phx)/(Lg+Lk))==0
    assert s.simplify(s.diff(U,Ph,2)-(1/Lk+1/Lg))==0
    assert s.simplify(Ph_eq.subs({n:0,Phx:0})/A+
       (2*m/q)*Lg/(Lg+Lk)*Om)==0
    Om_dot,Phx_dot,eta=s.symbols('Omega_dot Phi_ext_dot eta',real=True)
    Ph_dot=-s.diff(U,Ph)/eta
    Ud=s.diff(U,Ph)*Ph_dot+s.diff(U,Om)*Om_dot+s.diff(U,Phx)*Phx_dot
    assert s.simplify(Ud+s.diff(U,Ph)**2/eta-
       s.diff(U,Om)*Om_dot-s.diff(U,Phx)*Phx_dot)==0
    assert s.simplify(s.diff(U,Om)+(2*m*A/q)*I)==0
    assert s.simplify(s.diff(U,Phx)+(Ph-Phx)/Lg)==0
    Ueq=s.factor(U.subs(Ph,Ph_eq))
    step=s.factor(Ueq.subs(n,n+1)-Ueq)
    assert s.simplify(step-Ph0*(2*(f-Phx)+Ph0)/(2*(Lg+Lk)))==0
    tau=s.simplify(eta/(1/Lk+1/Lg))
    assert s.simplify(tau-eta*Lk*Lg/(Lk+Lg))==0
    print('PASS exact rotating fluxoid constraint, London equilibrium, phase-slip energy, work ledger')
    print('Phi_eq=',Ph_eq)
    print('dU/dt = mechanical port + applied flux port - (dU/dPhi)^2/eta')
    print('tau_eff =',tau)
    print('OPEN phase slip rates, YBCO TDGL, material inductances and probe fields')
if __name__=='__main__':main()
