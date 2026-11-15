#!/usr/bin/env python3
"""Non-operational source/observation negative controls for three mechanisms.
No microwave emitter, acoustic beam, DEW, or exposure design is provided.
"""
from dataclasses import dataclass
import numpy as np
@dataclass
class Observed:
    airborne_pressure_proxy: np.ndarray
    material_pressure_proxy: np.ndarray
    electronics_state: np.ndarray
    microphone_signal: np.ndarray
def causal_shift(x,steps):
    if steps<0:raise ValueError("future-to-past operation forbidden")
    out=np.zeros_like(x,dtype=float)
    if steps<len(x):out[steps:]=x[:len(x)-steps] if steps else x
    return out
def model(ultrasonic_envelope,absorbed_heat,induced_electronic_voltage):
    a,h,e=(np.asarray(v,dtype=float) for v in
           (ultrasonic_envelope,absorbed_heat,induced_electronic_voltage))
    if len(a)!=len(h) or len(a)!=len(e):raise ValueError("unmatched time indexing")
    # Abstract observation channels, NOT physically parameterised constitutive laws.
    air=causal_shift(a*a,2)
    material=causal_shift(np.diff(np.r_[0,h]),3)
    electronics=causal_shift(np.tanh(e),1)
    return Observed(air,material,electronics,air+electronics)
def tests():
    n=40;z=np.zeros(n);pulse=np.zeros(n);pulse[10]=1
    x=model(pulse,z,z)
    assert x.microphone_signal[10]==0 and x.airborne_pressure_proxy[12]>0
    y=model(z,pulse,z)
    assert abs(y.material_pressure_proxy).max()>0
    assert abs(y.microphone_signal).max()==0
    e=model(z,z,pulse)
    assert e.microphone_signal[11]>0
    q=model(pulse,pulse,pulse)
    assert np.allclose(q.microphone_signal,q.airborne_pressure_proxy+q.electronics_state)
    try:causal_shift(pulse,-1);raise AssertionError("negative delay accepted")
    except ValueError:pass
    try:model(np.zeros(n),np.zeros(n-1),z);raise AssertionError("unequal clocks accepted")
    except ValueError:pass
    print("PASS 6/6 abstract non-operational transduction controls")
if __name__=='__main__':tests()
