#!/usr/bin/env python3
"""Source-replay pump-off bands and causal competing acoustic fits.
Usage: python scripts/check_smith_filsinger_pumpoff_source_models.py original.mp3
No claimed physical propagation delay or natural-source energy measurement.
"""
import sys,json,hashlib
import numpy as np
from scipy import signal
from scipy.optimize import least_squares
import soundfile as sf

def read(path):
 x,fs=sf.read(path)
 if x.ndim>1:x=x.mean(axis=1)
 if fs!=44100 or not 105.79<len(x)/fs<105.80:
  raise ValueError('Expected original 105.8s, 44100Hz reel')
 return signal.resample_poly(x,1,2),fs//2

def bands(x,fs,n=2048):
 a,b=59.6,61.3
 f,t,z=signal.stft(x[int(a*fs):int(b*fs)],fs,nperseg=n,
                   noverlap=n-64,boundary=None,padded=False)
 t=t+a
 def rms(lo,hi):
  return np.sqrt(np.mean(np.abs(z[(f>=lo)&(f<hi)])**2,axis=0))
 return t,rms(7600,7950),rms(7950,8400),rms(5500,7500)

def pulse(t,t0,delay,shape):
 u=np.maximum(t-t0,0);v=np.maximum(u/delay,1e-16)
 return np.where(t>t0,np.exp(shape*(1+np.log(v)-v)),0.)

def one(p,t):
 b,a,t0,d,k=p
 return b+a*pulse(t,t0,d,k)

def two(p,t):
 b,a1,t0,d1,k1,a2,flight,d2,k2=p
 return b+a1*pulse(t,t0,d1,k1)+a2*pulse(t,t0+flight,d2,k2)

def independent(p,t):
 b,a1,c1,s1,a2,c2,s2=p
 return b+a1*np.exp(-.5*((t-c1)/s1)**2)+a2*np.exp(-.5*((t-c2)/s2)**2)

def compute(path):
 x,fs=read(path);t,c,u,l=bands(x,fs)
 windows={}
 for name,a,b in [('pre',59.7,59.95),('transition',60.4,60.6),
                  ('post',60.7,60.9)]:
  m=(t>=a)&(t<b)
  windows[name]={'carrier':float(np.mean(c[m])),'upper':float(np.mean(u[m])),
                 'lower':float(np.mean(l[m]))}
 assert windows['post']['upper']/windows['pre']['upper']>15
 assert windows['post']['carrier']/windows['pre']['carrier']<.05
 assert windows['transition']['lower']/windows['pre']['lower']>10
 gaps=[]
 for n in (1024,1536,2048,3072,4096):
  tn,_,un,_=bands(x,fs,n);m=(tn>=60.22)&(tn<=61.1)
  ti=tn[m];q=un[m]
  ix,_=signal.find_peaks(q,prominence=.2*q.max(),
                         distance=int(.12*fs/64))
  peaks=sorted(sorted(ix,key=lambda i:-q[i])[:2])
  if len(peaks)!=2:raise AssertionError('Strong peak pair absent')
  gaps.append(float(ti[peaks[1]]-ti[peaks[0]]))
 assert .28<min(gaps) and max(gaps)<.32
 m=(t>=60.26)&(t<=61.2)
 time=t[m];obs=u[m]/u[m].max()
 specs={
  'single_causal':(one,[.03,.9,60.35,.05,2],
     [[0,0,60.25,.01,.5],[.35,2,60.45,.3,12]]),
  'one_switch_two_paths':(two,[.03,.9,60.345,.06,2,.8,.30,.1,3],
     [[0,0,60.25,.01,.5,0,.1,.01,.5],[.35,2,60.45,.3,12,2,.5,.25,12]]),
  'two_unrelated_pulses':(independent,[.05,.9,60.42,.05,.8,60.74,.07],
     [[0,0,60.30,.015,0,60.60,.015],[.35,2,60.52,.2,2,60.95,.25]])}
 fits={}
 for name,(fn,start,bounds) in specs.items():
  best=None
  for dt in (0,-.006,.006):
   p=np.array(start,dtype=float)
   if name!='two_unrelated_pulses':p[2]+=dt
   fit=least_squares(lambda p:fn(p,time)-obs,p,bounds=bounds,max_nfev=2000)
   if best is None or np.sum(fit.fun**2)<np.sum(best.fun**2):best=fit
  pred=fn(best.x,time);ss=float(np.sum((obs-pred)**2))
  tot=np.sum((obs-np.mean(obs))**2)
  fits[name]={'r2_in_sample':float(1-ss/tot),
              'params':[float(z) for z in best.x],
              'number_parameters':len(best.x)}
 assert fits['one_switch_two_paths']['r2_in_sample']>.9
 assert fits['single_causal']['r2_in_sample']<.6
 return {'SHA256':hashlib.sha256(open(path,'rb').read()).hexdigest(),
         'duration_s':len(x)/fs,'windows':windows,
         'robust_peak_separation_s':gaps,'model_fits':fits,
         'scope':'Acoustic envelope only: feedback origin and source work unmeasured.'}

if __name__=='__main__':
 if len(sys.argv)!=2:raise SystemExit('Supply original reel audio path')
 print(json.dumps(compute(sys.argv[1]),indent=2))
 print('PASS source-acoustic multi-band and causal fit discriminator')
