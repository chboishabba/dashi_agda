#!/usr/bin/env python3
"""Source-specific abstract *observation* operators, not physical weapon designs,
full HAARP plasma solvers or Filsinger experimental power measurements.
"""
import numpy as np
from scipy import signal

def whistlerGrowthOnsetConditional(attenuation_db=14.,onset_delay_s=1.):
    # Paper reports onset sensitivity. An unchanged-threshold exponential
    # is OUR simplified inverse model, not the paper's inferred coefficient.
    ratio=10**(attenuation_db/20)
    return {'source_amplitude_factor':float(ratio),
            'conditional_growth_per_second':float(np.log(ratio)/onset_delay_s)}

def geometricPowerComparison(lower_db=5.,upper_db=7.):
    # Cohen 2011 source-specific modeled injected POWER, not gain of a coil.
    return 10**(lower_db/10),10**(upper_db/10)

def ionosphericTwoStageRetarded(x,first_flight,second_flight,
                               attenuation=.7,natural_hall=None):
    x=np.asarray(x,dtype=float)
    if min(first_flight,second_flight)<0:raise ValueError('future propagation')
    def shift(v,k):
        y=np.zeros_like(v)
        if k<len(y):y[k:]=v[:-k] if k else v
        return y
    ms=attenuation*shift(x,first_flight)
    hall=attenuation*shift(ms,second_flight)
    if natural_hall is not None:hall=hall+np.asarray(natural_hall)
    return ms,hall

def acousticDifferenceFrequency(fs=512,seconds=2,f1=80,f2=91):
    t=np.arange(int(fs*seconds))/fs
    primary=np.cos(2*np.pi*f1*t)+np.cos(2*np.pi*f2*t)
    quadratic=primary**2
    observer=signal.sosfiltfilt(signal.butter(4,30,fs=fs,btype='low',output='sos'),quadratic)
    return t,primary,observer

def thermoelasticObservation(absorbed_heat,flight_samples=2):
    # Synthetic material response from heat to pressure proxy; not human
    # exposure guidance, source targeting or free-air microphone prediction.
    x=np.asarray(absorbed_heat,dtype=float)
    if flight_samples<0:raise ValueError('future propagation')
    gradient=np.diff(np.r_[0.,x]);p=np.zeros_like(gradient)
    if flight_samples<len(p):
        p[flight_samples:]=gradient[:-flight_samples] if flight_samples else gradient
    return p

def tests():
    onset=whistlerGrowthOnsetConditional()
    assert abs(onset['conditional_growth_per_second']-1.611809565)<1e-5
    lo,hi=geometricPowerComparison()
    assert 3.16<lo<3.17 and 5.0<hi<5.02
    seed=np.zeros(25);seed[2]=1
    ms,hall=ionosphericTwoStageRetarded(seed,3,5)
    assert ms[5]>.69 and hall[10]>.48 and not np.any(hall[:10])
    nat=np.zeros(25);nat[4]=1
    _,hall2=ionosphericTwoStageRetarded(np.zeros(25),3,5,natural_hall=nat)
    assert np.array_equal(hall2,nat)
    t,primary,low=acousticDifferenceFrequency()
    f,p=signal.periodogram(low,fs=512)
    m=(f>2)&(f<30)
    assert abs(f[m][np.argmax(p[m])]-11)<1e-9
    h=np.zeros(15);h[5]=1
    out=thermoelasticObservation(h)
    assert out[5]==0 and out[7]==1 and out[8]==-1
    try:thermoelasticObservation(h,-1)
    except ValueError:pass
    else:raise AssertionError('negative flight accepted')
    print('PASS 7/7 source-specific conditional forward-operator tests')

if __name__=='__main__': tests()
