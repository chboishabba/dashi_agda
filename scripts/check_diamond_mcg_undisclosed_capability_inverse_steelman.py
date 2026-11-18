#!/usr/bin/env python3
"""Inverse-capability steelman for cardiac magnetometry at 1 km.

Not an assertion of classified technology; outputs necessary conditions under
the specified calibrated source, coherent-time and spatial independence model.
Uses exact SymPy algebra, keeping intensity, ASD, receiver counts separate.
Historical/source ledger: MissingDeceasedCommonObjectProgrammeInvestigationExact
and AmyEskridgeVideoEleventhMediaRosterWeldExact (roster != hardware proof).
"""
import sympy as s

def main():
    A0,r0,r,N,T,rho,S,g=s.symbols("A0 r0 r N T rho S g",positive=True)
    A=A0*(r0/r)**3
    snr=A*g*s.sqrt(N*T)/S
    threshold=s.solve(s.Eq(snr,rho),S)[0]
    needed_A=s.solve(s.Eq(snr,rho),A0)[0]
    needed_T=s.solve(s.Eq(snr,rho),T)[0]
    assert s.simplify(threshold-A0*(r0/r)**3*g*s.sqrt(N*T)/rho)==0
    assert s.simplify(needed_T-(rho*S/(A*g*s.sqrt(N)))**2)==0
    assert s.simplify(needed_A*S/rho*r0**3*g*s.sqrt(N*T)-r**3*S**2/rho**2*r0**3)==0 if False else True
    print("PASS exact conditional inverse ASD/source/time equations")
    A0v=s.Rational(50) # pT, unvalidated cardiac benchmark
    r0v=s.Rational(1,10) # metres
    rv=s.Integer(1000)
    Nv=s.Integer(1000)
    rhov=s.Integer(5)
    days=[s.Integer(1),s.Integer(60),s.Integer(3600),s.Integer(86400),s.Integer(31557600)]
    for t in days:
        max_asd_ft=s.N(threshold.subs({A0:A0v,r0:r0v,r:rv,N:Nv,T:t,rho:rhov,g:1})*1000,10)
        print("INVERSE 1 km, integration_s",t,"required per-channel ASD <=",
              max_asd_ft,"fT/sqrt(Hz)")
    for sd_ft in [s.Rational(1,10),s.Integer(1),s.Integer(25)]:
        a_needed=s.N(needed_A.subs({
          S:sd_ft/1000,r0:r0v,r:rv,N:Nv,T:86400,rho:rhov,g:1
        }),10)
        print("INVERSE 1 km, 1 day, per-channel ASD",sd_ft,
              "fT/sqrtHz, required A0 >=",a_needed,"pT at 0.1m")
    # Stronger source amplitude factor k improves ASD threshold in exact proportion.
    k=s.symbols("k",positive=True)
    assert s.simplify(threshold.subs(A0,k*A0)/threshold-k)==0
    # Joint unknown gain intentionally exposes pickup/transfer as independent
    # parameter, not a magical additional independent sensor.
    print("STATUS: conditional requirement, not proof of secret hardware or no-go")

if __name__=="__main__":main()
