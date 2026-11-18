#!/usr/bin/env python3
"""Tajmar observables: preserve observed Nb phase contrast vs gyro non-Tc onset.

Primary: M Tajmar et al 2007, arXiv:0707.3806 pp4-5,7,9-10.
The published accelerometer ratio contrast at low vs higher temperature does
not imply the gyroscope onset coincides with material Tc. The reported negative
signs and uncertainties are kept explicit; no interpretation as gravity.
"""
import sympy as s

def check():
    low=s.Rational(-226,10_000_000_000)   # -2.26e-8
    higher=s.Rational(-124,100_000_000_000) # -1.24e-9
    assert s.simplify(low/s.Rational(1,10**8)+s.Rational(226,100))==0
    assert s.simplify(higher/s.Rational(1,10**9)+s.Rational(124,100))==0
    assert abs(low)>abs(higher)
    assert abs(low/higher)>18
    # Nb accelerometer experiment contrasted 4.5-6.5K and 10-14K.
    # A later gyro temperature onset was reported around 16K for Nb/Al,
    # around 32K for YBCO, not the actual superconducting Tc.
    nb_gyro_onset=s.Integer(16)
    ybco_gyro_onset=s.Integer(32)
    nb_tc=s.Rational(92,10) # approximate conventional Nb Tc 9.2K
    al_tc=s.Rational(12,10) # approximate pure aluminum Tc 1.2K
    assert nb_gyro_onset!=nb_tc and nb_gyro_onset!=al_tc
    assert ybco_gyro_onset>nb_gyro_onset
    print('PASS separate accelerometer phase contrast and gyroscope onset')
    print('Nb acceleration response ratio magnitudes:',s.N(abs(low/higher),8))
    print('CAUTION: approximate reference Tc values and published gyro onset, not same raw source')
    print('OPEN helium-vibration/reference subtraction and original time histories')

if __name__=='__main__':check()
