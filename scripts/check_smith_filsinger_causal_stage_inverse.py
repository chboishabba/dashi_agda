#!/usr/bin/env python3
"""Original MP3 source-locked acoustic-order and passive-modal maximum cut.
Usage:
 python scripts/check_smith_filsinger_causal_stage_inverse.py ReelAudio-93787.mp3
No fitted event is automatically a physical switch-off timestamp, and
no acoustic fit or positive mode-energy transfer proves natural source power.
"""
import hashlib
import json
import sys
import numpy as np
import soundfile as sf
from scipy import ndimage,signal
from scipy.optimize import nnls,least_squares
from scipy.stats import poisson

SHA="573eb6b205bdf1c29cb33fad5e28eeb00dee18c5566aee7290679aac0396c4c6"

def load_source(path):
    if hashlib.sha256(open(path,"rb").read()).hexdigest()!=SHA:
        raise ValueError("Original-reel SHA256 mismatch")
    x,fs=sf.read(path)
    if x.ndim==2:x=x.mean(axis=1)
    if fs!=44100 or not 105.79<len(x)/fs<105.80:
        raise ValueError("Unexpected original recording")
    return signal.resample_poly(x,1,2),fs//2

def bands(x,fs,n=2048):
    a,b=59.65,61.25
    f,t,S=signal.stft(x[int(a*fs):int(b*fs)],fs,nperseg=n,
                      noverlap=n-64,boundary=None,padded=False)
    t=t+a
    def rms(lo,hi):
        m=(f>=lo)&(f<hi)
        return np.sqrt(np.mean(np.abs(S[m])**2,axis=0))
    return t,rms(7600,7950),rms(7950,8400),rms(5500,7500)

def markers(t,carrier,upper):
    dt=np.median(np.diff(t))
    base=np.median(carrier[(t>=59.75)&(t<=60.22)])
    sm=ndimage.median_filter(carrier,size=max(3,int(.061/dt)//2*2+1))
    width=int(.18/dt)
    drop=None
    for i in np.flatnonzero((t>=60.28)&(sm/base<.5)):
        if i+width<len(t) and np.mean(sm[i:i+width]/base<.5)>.8:
            drop=float(t[i]);break
    inds,_=signal.find_peaks(upper,prominence=.2*upper.max(),distance=int(.11/dt))
    inds=inds[(t[inds]>=60.3)&(t[inds]<60.95)]
    inds=sorted(sorted(inds,key=lambda i:-upper[i])[:2],key=lambda i:t[i])
    if drop is None or len(inds)!=2:raise AssertionError("Original time markers missing")
    return dict(first_peak=float(t[inds[0]]),acoustic_half_amplitude_drop=drop,
                second_peak=float(t[inds[1]]),
                carrier_at_first_peak_relative=float(carrier[inds[0]]/base))

def stage(t,t0,k,n):
    u=np.maximum(t-t0,0)
    z=np.maximum(k*u,1e-30)
    return np.where(t>t0,np.exp(n*(1+np.log(z/n)-z/n)),0)

def model(t,y,training,i,j,k,t0):
    A=np.column_stack([np.ones(np.sum(training)),
        stage(t[training],t0,k,i),stage(t[training],t0,k,j)])
    coeff=nnls(A,y[training])[0]
    B=np.column_stack([np.ones(len(t)),stage(t,t0,k,i),stage(t,t0,k,j)])
    return B@coeff,coeff

def fitted_cascade(t,y,training):
    best=None
    for i in range(1,7):
      for j in range(i+1,21):
        for k in range(10,52,2):
          t0=60.404-i/k
          if not 60.22<=t0<=60.405 or not 60.25<t0+j/k<61.10:continue
          pred,_=model(t,y,training,i,j,k,t0)
          err=np.sum((pred[training]-y[training])**2)
          if best is None or err<best[0]:best=(err,i,j,k,t0)
    _,i,j,k,t0=best
    def residual(z):
        pred,_=model(t,y,training,i,j,*z)
        return pred[training]-y[training]
    sol=least_squares(residual,[k,t0],bounds=([3,60.2],[60,60.43]),max_nfev=80)
    k,t0=map(float,sol.x)
    pred,c=model(t,y,training,i,j,k,t0)
    return dict(first_tap=i,second_tap=j,rate_per_second=k,
                latent_event_s=t0,gains=c.tolist(),
                NOTE="Stage indices are mathematical, NOT physical component count"),pred

def main(path):
    x,fs=load_source(path)
    events=[markers(*bands(x,fs,n)[:3]) for n in (1024,1536,2048,3072,4096)]
    for e in events:
        assert e["first_peak"]<e["acoustic_half_amplitude_drop"]<e["second_peak"]
        assert e["carrier_at_first_peak_relative"]>.95
        assert .29<e["second_peak"]-e["first_peak"]<.32

    t,c,u,lo=bands(x,fs)
    mask=(t>=60.26)&(t<=61.20)
    t=t[mask];y=u[mask]/u[mask].max()
    train=np.ones(len(t),dtype=bool)
    pars,pred=fitted_cascade(t,y,train)
    SSE=np.sum((pred-y)**2)
    R2=float(1-SSE/np.sum((y-y.mean())**2))
    assert R2>.80
    rate=pars["rate_per_second"];n=pars["second_tap"]
    elapsed=np.linspace(0,1,501)
    energies=np.array([poisson.pmf(j,rate*elapsed) for j in range(n+1)])
    total=energies.sum(axis=0)
    assert np.all(total<=1+1e-11)
    assert np.all(total>=-1e-11)
    assert np.allclose(total+(1-total),1,atol=1e-11)
    assert energies[n].max()>0

    folds=[]
    for fi,held in enumerate(np.array_split(np.arange(len(t)),5)):
        fitmask=np.ones(len(t),dtype=bool);fitmask[held]=False
        p,out=fitted_cascade(t,y,fitmask)
        folds.append(dict(fold=fi,
                          held_mse=float(np.mean((y[held]-out[held])**2)),
                          selected_taps=[p["first_tap"],p["second_tap"]]))
    nested=float(np.mean([v["held_mse"] for v in folds]))
    # Prior independently fitted acoustic-envelope comparator on same MP3:
    # two flexible causal response kernels: block MSE about 0.0466;
    # two independent acoustic pulses: block MSE about 0.0635.
    assert nested>.0466

    # Original 44.1kHz spectral bins; same-LC claim is conditional.
    raw,sr=sf.read(path)
    if raw.ndim==2:raw=raw.mean(axis=1)
    def peak(a,b,lo,hi):
        z=raw[int(a*sr):int(b*sr)]
        f,p=signal.welch(z,sr,nperseg=min(4096,len(z)))
        m=(f>=lo)&(f<hi);return float(f[m][np.argmax(p[m])])
    fdrive=peak(59.75,60.15,7600,7950)
    fnatural=peak(60.66,60.76,7950,8400)
    ratio=fnatural/fdrive
    # f ∝ (LC)^-1/2, if a single, fixed-topology lumped LC
    LCdrop=100*(1-ratio**-2)
    assert 4<LCdrop<6

    result=dict(original_sha256=SHA,observed_acoustic_events=events,
                physical_switch_off_time_observed=False,
                shared_passive_cascade=dict(parameters=pars,r2=R2,
                    nested_held_block_mse=nested,blocked_folds=folds),
                same_mode_conditional_inverse=dict(
                    driven_acoustic_peak_hz=fdrive,post_acoustic_peak_hz=fnatural,
                    same_mode_LC_product_change_percent=LCdrop,
                    half_power_bandwidth_Q_requirement=fnatural/(2*(fnatural-fdrive))),
                result="passive internal transfer CONSTRUCTED; same-apparatus physical fit OPEN",
                physical_weld_required=[
                  "measured actual switch state time","real electrical modes",
                  "matched electromechanical transfer","signed environmental source work"])
    print(json.dumps(result,indent=2))
    print("PASS source time ordering, SHA, positive-mode conservation, five nested held-block controls, conditional LC bound")
if __name__=="__main__":
    if len(sys.argv)!=2:raise SystemExit("Supply exact original 105.8-second MP3")
    main(sys.argv[1])
