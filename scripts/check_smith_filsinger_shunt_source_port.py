#!/usr/bin/env python3
"""Source-qualified Filsinger shunt and finite-source max-cut.
All input parameters here are CONDITIONAL; capacitor display != source Voc.
Run with python3 scripts/check_smith_filsinger_shunt_source_port.py.
Dependencies: sympy, numpy (existing DASHI physics stack).
"""
from math import sqrt
import numpy as np
import sympy as sp

def exact_port_power():
    v,i,r=sp.symbols("Voc I R",real=True,nonzero=True)
    delivered=(v-r*i)*i
    pmax=v*v/(4*r)
    slack=r*(i-v/(2*r))**2
    assert sp.simplify(pmax-delivered-slack)==0
    # If r>0 this is a nonnegative square. Arbitrarily timed terminal
    # current/impedance control cannot beat this unchanged-source bound.
    return True

def shunt_power(voltage_rms,ohms,n):
    return n*voltage_rms**2/ohms

def cap_stored_j(volts,farads):
    return farads*volts**2/2

def source_r_required(v_oc_rms,p_target):
    return v_oc_rms**2/(4*p_target)

def recover_stationary_source(v1,i1,v2,i2):
    if abs(i2-i1)<1e-12:raise ValueError("different loaded currents required")
    r=(v1-v2)/(i2-i1)
    if r<=0:raise ValueError("not a fixed passive positive-R source")
    return v1+r*i1,r

def global_droop(cap_f,power,seconds=1800,initial_volts=250000):
    e=power*seconds
    if 2*e/cap_f>=initial_volts**2:raise ValueError("reservoir exhausted")
    return (2*e/cap_f)/(initial_volts+sqrt(initial_volts**2-2*e/cap_f))

def test():
    assert exact_port_power()
    assert shunt_power(1500,1e6,1)==2.25
    assert shunt_power(1500,1e6,2)==4.5
    assert shunt_power(1500,1e6,3)==6.75
    assert abs(shunt_power(1500/sqrt(2),1e6,3)-3.375)<1e-12
    assert shunt_power(750,1e6,3)==1.6875
    assert shunt_power(1500,2e6,3)==3.375
    assert shunt_power(1500,4e6,3)==1.6875
    assert abs(cap_stored_j(1500,3.3e-6)-3.7125)<1e-10
    for v,p,expected_r in [(1,.4,.625),(10,.4,62.5),(48,.4,1440),
                            (48,6.7,48**2/(4*6.7)),(48,1000,.576)]:
        assert abs(source_r_required(v,p)-expected_r)<1e-10
    for voc,r in [(2,40),(48,1440),(10,5000)]:
        i1=voc/(2*r);i2=voc/(3*r)
        vv,rr=recover_stationary_source(voc-r*i1,i1,voc-r*i2,i2)
        assert abs(vv-voc)<1e-9 and abs(rr-r)<1e-9
    rng=np.random.default_rng(20)
    V=rng.uniform(-30,30,1000);R=rng.uniform(.2,2000,1000)
    I=rng.normal(0,.4,1000)
    P=(V-R*I)*I
    limit=V**2/(4*R)
    assert np.all(P<=limit+1e-9)
    # 2025 source model is global DC capacitor: NOT the 7.83Hz mode.
    assert abs(global_droop(2.47,.4)-.0011659919)<1e-9
    assert .004<global_droop(.7,.4)<.005
    assert abs(.5*2.47*250000**2/1e9-77.1875)<1e-8
    assert abs(.4/(250000*2e-12)/1e6-.8)<1e-10
    # A 1,500 V display alone cannot distinguish natural recharge
    # from driven charging, nor does it give environmental Voc.
    return True

if __name__=="__main__":
    test()
    print("PASS exact stationary-port completion-square, shunt and global-C source controls")
