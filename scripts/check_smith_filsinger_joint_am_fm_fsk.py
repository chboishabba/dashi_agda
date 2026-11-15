#!/usr/bin/env python3
"""Original DASHI synthetic controls for joint AM/FM/FSK/nonlinear observation.
All six tests use synthetic signals, not inferred physical source powers.
Actual Filsinger audio SHA and inverse analysis: accompanying report.
"""
import numpy as np
from scipy import signal as s
R=500
t=np.arange(20*R)/R

def bandpower(x,lo,hi):
    f,p=s.welch(x,R,nperseg=4000,noverlap=2000)
    m=(f>=lo)&(f<=hi)
    return np.trapezoid(p[m],f[m])

def observables(z):
    am=np.log(np.maximum(abs(z),1e-9))
    phase=np.unwrap(np.angle(z))
    fm=np.gradient(phase)*R/(2*np.pi)
    return am,fm

def test_pure_am():
    a,f=observables((1+.25*np.cos(2*np.pi*1.125*t)).astype(complex))
    assert bandpower(a,.6,2)>1e-3 and np.max(abs(f))<1e-7

def test_pure_fm():
    fi=4*np.cos(2*np.pi*3.9*t)
    a,f=observables(np.exp(1j*2*np.pi*np.cumsum(fi)/R))
    assert np.std(a)<1e-12 and bandpower(f,3,5)>1

def test_joint_am_fm():
    fi=4*np.cos(2*np.pi*3.9*t)
    z=(1+.25*np.cos(2*np.pi*1.125*t))*np.exp(1j*2*np.pi*np.cumsum(fi)/R)
    a,f=observables(z)
    assert bandpower(a,.6,2)>20*bandpower(a,3,5)
    assert bandpower(f,3,5)>20*bandpower(f,.6,2)

def test_phase_continuous_fsk():
    fi=3*np.sign(np.cos(2*np.pi*1.25*t))
    phase=2*np.pi*np.cumsum(fi)/R
    assert np.max(abs(np.diff(phase)))<.05
    _,f=observables(np.exp(1j*phase))
    assert np.quantile(f,.75)>2 and np.quantile(f,.25)<-2

def test_mode_beating():
    z=np.exp(1j*2*np.pi*2*t)+.5*np.exp(-1j*2*np.pi*2*t)
    a,f=observables(z)
    assert bandpower(a,3,5)>1e-4 and bandpower(f,3,5)>1e-3

def test_drift_is_not_am():
    fi=np.linspace(-15,20,len(t))
    z=np.exp(1j*2*np.pi*np.cumsum(fi)/R)
    a,f=observables(z)
    assert np.std(a)<1e-12
    assert np.allclose(np.diff(f)[100:-100],np.diff(fi)[100:-100],atol=.02)

if __name__=="__main__":
    for fn in [test_pure_am,test_pure_fm,test_joint_am_fm,
               test_phase_continuous_fsk,test_mode_beating,test_drift_is_not_am]:
        fn()
        print("PASS",fn.__name__)
