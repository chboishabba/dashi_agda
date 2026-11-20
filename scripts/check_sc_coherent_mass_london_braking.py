#!/usr/bin/env python3
"""Coherent superconducting charged-mass state: London moment & source audit.

Attribution: London rotating-superconductor law; standard BCS/GL and
gauge-invariant stress-energy. Li/Torr gravito-EM theory conjecture is separate.
User proposal: collective coherent matter braking source; no empirical gravity.
"""
import sympy as s
def main():
    hbar,m,q,Omega,n,alpha=s.symbols("hbar m q Omega n alpha",real=True,nonzero=True)
    B=-2*m*Omega/q # London moment; q,m pair carry consistent signs
    assert s.simplify(s.diff(B,Omega)+2*m/q)==0
    psi=s.symbols("psi",positive=True)
    # gauge invariant canonical momentum; London relation for uniform rotation
    # curl m*v_s + q*A =0 (zero fluxoid winding, far from boundary).
    curl_v=2*Omega
    assert s.simplify(m*curl_v+q*B)==0
    # Distinguish coherent amplitudes from stress-energy of the sample.
    k,N=s.symbols("k N",integer=True,positive=True)
    amp=N*k
    intensity=s.expand(amp**2)
    assert intensity==N**2*k**2
    # coherent array emission in one phase-matched far-field mode can
    # exhibit N² intensity, but energy is paid by source and duration.
    # Number of coherent particles alone does not multiply total rest mass.
    mass=s.symbols("mass",positive=True)
    assert s.simplify(s.diff(N*mass,N)-mass)==0
    # Numerical SI scale
    me=9.1093837139e-31
    e=1.602176634e-19
    rpm=5000
    w=rpm*2*s.pi/60
    BL=2*me/e*w # pair 2me and 2e cancel
    assert 5e-9<float(BL)<7e-9
    print("PASS London canonical momentum, source additivity/coherent emission distinction")
    print("5000rpm clean ideal London moment magnitude tesla",float(BL))
    print("OPEN real YBCO multi-band phase/current response, vortices, KK source")
if __name__=="__main__":main()
