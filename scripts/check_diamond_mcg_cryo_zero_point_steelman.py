#!/usr/bin/env python3
"""Cryogenic MCG steelman: temperature, zero-point and receiver comparisons.

Physics boundaries:
- A quantum harmonic mode has E_n=(n+1/2)hf (same mode-hyperfabric as PR #701).
- coth(hf/(2kT)) is the equilibrium symmetrized harmonic-mode noise factor,
  NOT the universal magnetic instrument PSD and NOT a PSD lower bound.
- Cardiac field amplitude, phase, geometry, receiver noise and shielding must
  be calibrated independently. SQUID noise examples are conditional receivers.
- No thermally equilibrated alive human heart at T=0 K is assumed.
"""
import sympy as s

def exact():
    n,q=s.symbols('n q',positive=True)
    E=(n+s.Rational(1,2))*q
    assert s.simplify(E.subs(n,0)-q/2)==0
    assert s.simplify(E-E.subs(n,0)-n*q)==0
    u=s.symbols('u',positive=True)
    assert s.simplify(s.coth(u/2).rewrite(s.exp)-(1+2/(s.exp(u)-1)))==0
    r,d=s.symbols('r d',positive=True)
    attenuation=(r/(r+d))**3
    assert s.simplify(attenuation**(-2)-((r+d)/r)**6)==0
    S1,S2=s.symbols('S1 S2',positive=True)
    assert s.simplify((S1/S2)**2*(S2/S1)**2-1)==0
    print('PASS exact ground/excitation, harmonic coth occupancy, standoff r^6 cost')

def run():
    exact()
    h=6.62607015e-34
    kb=1.380649e-23
    print('Quantum thermal crossover hf/k at 1 Hz (K):',h/kb)
    for freq in (1,10,100):
        print(f'crossover f={freq} Hz: {h*freq/kb:.6g} K')
    a0_pt=50.
    r0=.1
    n=1000
    rho=5.
    seconds_per_year=365.25*86400
    noise_cases=[('NV illustrative',7.0),('improved NV hypothetical',1.0),
                 ('SQUID-like hypothetical',.001),('extreme receiver hypothetical',.00001)]
    for name,asd in noise_cases:
        print(name,'ASD pT/sqrt(Hz)',asd)
        for r in (10.,100.,1000.):
            a=a0_pt*(r0/r)**3
            time_s=(rho*asd/(a*n**.5))**2
            print(f'  r={r:g} m coherent T={time_s:.8g} s = {time_s/seconds_per_year:.8g} y')
    for r,d in [(1.,.1),(10.,.1),(10.,1.),(1000.,1.)]:
        print(f'standoff r={r:g}m extra={d:g}m: time factor {(1+d/r)**6:.6g}')
    print('PASS symbolic and conditional range arithmetic')
    print('OPEN: receiver magnetic PSD vs frequency, dilution-refrigerator viability,')
    print('      actual cardiac source, thermodynamic readout/cooling, photon statistics,')
    print('      heart-rate phase stability and source-attribution false alarms')

if __name__=='__main__':run()
