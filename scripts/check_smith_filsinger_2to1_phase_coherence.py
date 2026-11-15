#!/usr/bin/env python3
"""Source-required 2:1 phase-coupling test of 3–5Hz and 6–10Hz acoustic FM/AM.
No claimed identification of electrical current or environmental source.
Usage: python check_smith_filsinger_2to1_phase_coherence.py /path/to/carrier_time_trace_50Hz.csv
"""
import sys,json
from pathlib import Path
import numpy as np
from scipy import signal
def phase_locking(series,fs=50,shifts=2000,seed=53):
    x=signal.detrend(np.asarray(series,dtype=float))
    def ph(lo,hi):
        sos=signal.butter(3,(lo,hi),btype='bandpass',fs=fs,output='sos')
        return np.angle(signal.hilbert(signal.sosfiltfilt(sos,x)))
    lower=ph(3,5)[125:-125];upper=ph(6,10)[125:-125]
    n=len(lower)
    if n<=4*fs:raise ValueError('Audio active interval too short')
    obs=np.abs(np.mean(np.exp(1j*(2*lower-upper))))
    rng=np.random.default_rng(seed)
    null=[np.abs(np.mean(np.exp(1j*(2*lower-np.roll(upper,int(k))))))
          for k in rng.integers(2*fs,n-2*fs,size=shifts)]
    return dict(phase_lock_value=float(obs),shift_null_median=float(np.median(null)),
                uncorrected_shift_p=float((1+sum(v>=obs for v in null))/(1+shifts)))
if __name__=='__main__':
    if len(sys.argv)!=2:raise SystemExit('Supply original 50Hz carrier_trace.csv path')
    trace=np.genfromtxt(Path(sys.argv[1]),delimiter=',',names=True)
    selected=(trace['recording_s']>=36.5)&(trace['recording_s']<=59.2)
    if sum(selected)<500:raise ValueError('Not enough user-audio carrier-active samples')
    print(json.dumps({'FM':phase_locking(trace['fast_deviation_hz'][selected]),
                      'AM':phase_locking(trace['carrier_intensity_relative_db'][selected]),
                      'scope':'acoustic phase only; not Earth electrical phase or natural source work'},indent=2))
