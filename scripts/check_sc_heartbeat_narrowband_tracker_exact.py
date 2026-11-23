#!/usr/bin/env python3
"""Heartbeat narrow-band response: exact mathematical coherence model.

This does NOT assert a real person's heartbeat stays phase coherent for T.
RQU (Phys Rev Research 7 013281, 2025) demonstrates dc/VHF to ~5GHz
upconversion and 46.9dB phase-sensitive extinction, NOT magnetic SNR gain.
"""
import sympy as s

def check():
    G,b0,b=s.symbols('G b0 b',positive=True)
    assert s.simplify((b0/G)*G-b0)==0
    assert s.simplify(s.solve(s.Eq(b0/G,b),b0)[0]-G*b)==0
    T,dfdt=s.symbols('T dfdt',positive=True)
    # F(t) = f0 + (df/dt)t ; residual phase after T relative to fixed f0
    residual=s.pi*dfdt*T**2
    assert s.simplify(s.diff(residual,T)-2*s.pi*dfdt*T)==0
    assert s.simplify(s.solve(s.Eq(residual,1),dfdt)[0]-1/(s.pi*T**2))==0
    assert s.simplify(residual.subs(T,100)/residual.subs(T,10)-100)==0
    print('100 Hz initial BW after 1076 gain:',float(s.Rational(100,1076)),'Hz')
    print('10 kHz initial BW after 1076 gain:',float(s.Rational(10000,1076)),'Hz')
    print('1 Hz postgain BW requires initial BW at least 1076 Hz')
    print('1 day coherent 1-rad linear chirp ceiling:',float(1/(s.pi*86400**2)),'Hz/s')
    print('PASS exact gain-bandwidth and chirp controls; source phase stability OPEN')

if __name__=='__main__':check()
