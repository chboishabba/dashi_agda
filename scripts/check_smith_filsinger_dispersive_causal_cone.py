#!/usr/bin/env python3
"""Abstract local finite-wave stencil with a strict discrete causal cone.
No unmeasured Earth wave speed or planet-scale propagation inferred.
"""
import numpy as np
def step(v,i,p,dt=.02,C=.85,L=.9,G=.006,R=.015,chi=.25,eta=.35,beta=.45):
 n=len(v)
 # New edge and node updates depend ONLY on previous neighbouring states.
 ii=i+dt/L*(v[:-1]-v[1:]-R*i)
 pdot=(v-p/chi-beta*p**3)/eta
 pp=p+dt*pdot
 flow=np.zeros(n)
 flow[0]-=i[0]
 flow[1:-1]+=i[:-1]-i[1:]
 flow[-1]+=i[-1]
 vv=v+dt/C*(flow-G*v-pdot)
 return vv,ii,pp
def check():
 n=31
 v=np.zeros(n);i=np.zeros(n-1);p=np.zeros(n)
 v[0]=1.
 for k in range(1,n):
  v,i,p=step(v,i,p)
  assert np.all(v[k+1:]==0)
  assert np.all(p[k+1:]==0)
  assert np.all(i[k:]==0)
 assert v[-1]==0
 for k in range(n,2*n+2):v,i,p=step(v,i,p)
 assert v[-1]!=0
 print('PASS discrete local causality and nonlinear polarisation domain of dependence')
if __name__=='__main__':check()
