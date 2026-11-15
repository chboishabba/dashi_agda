#!/usr/bin/env python3
"""Original-source 3-regime audio replay; never reinterpret mic spectra as watts.
Usage: python scripts/check_smith_filsinger_hybrid_audio.py ReelAudio-93787.mp3
Requires numpy scipy soundfile. No original recording is bundled in repo.
"""
import json,sys
import numpy as np
import soundfile as sf
from scipy import signal,stats
def audio(path):
    x,sr=sf.read(path);x=x.mean(axis=1) if x.ndim>1 else x
    if sr!=44100:raise ValueError('Original reel expected at 44100 Hz')
    if not 105.79<len(x)/sr<105.80:raise ValueError('Source is not the selected reel')
    return signal.resample_poly(x,1,2),sr//2
def bands(x,fs,a,b):
    seg=x[int(a*fs):int(b*fs)]
    f,t,Z=signal.stft(seg,fs,nperseg=1024,noverlap=896,
                         boundary=None,padded=False)
    z=np.abs(Z)
    def rms(lo,hi):return np.sqrt(np.mean(z[(f>=lo)&(f<hi)]**2,axis=0))
    return t+a,rms(7600,7950),rms(7950,8400),rms(5500,7500)
def replay(path):
    x,fs=audio(path)
    windows={'startup':(35.15,38.15),'hot':(51.3,56.4),
             'shutdown':(59.45,61.35)}
    report={'input_duration_s':len(x)/fs,'input_sr':fs,'regimes':{}}
    for name,(a,b) in windows.items():
        t,c,u,l=bands(x,fs,a,b)
        report['regimes'][name]={'frames':len(t),'start':float(t[0]),'end':float(t[-1])}
        if name=='shutdown':
            cells=[]
            for a,b in [(59.7,59.95),(60.1,60.3),(60.4,60.6),
                        (60.7,60.9),(61.05,61.25)]:
                idx=(t>=a)&(t<b)
                cm=float(np.mean(c[idx]))
                cells.append({'window_s':[a,b],
                  'upper_over_carrier':float(np.mean(u[idx])/cm),
                  'lower_over_carrier':float(np.mean(l[idx])/cm)})
            idx=(t>=60.34)&(t<=60.78)
            fit=stats.linregress(t[idx],np.log(np.maximum(c[idx],1e-12)))
            report['shutdown']={'window_ratios':cells,
                'log_amplitude_slope_per_s':float(fit.slope),
                'amplitude_pseudo_tau_s':float(-1/fit.slope),
                'fit_r_squared':float(fit.rvalue**2)}
            assert cells[0]['upper_over_carrier']<.05
            assert cells[3]['upper_over_carrier']>1
            assert .05<report['shutdown']['amplitude_pseudo_tau_s']<.2
    return report
if __name__=='__main__':
    if len(sys.argv)<2:raise SystemExit('specify original 105.8s MP3 path')
    result=replay(sys.argv[1]);print(json.dumps(result,indent=2))
    print('PASS: source audio segmented into startup, hot and multimode pump-off')
