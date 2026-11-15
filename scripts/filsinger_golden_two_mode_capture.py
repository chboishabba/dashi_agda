#!/usr/bin/env python3
"""Passive two-mode fixed-area rectangle comparison. Source spectra are SYNTHETIC.
No physical Earth/ionizing cosmic-ray source or Maxwell solution is claimed.
Uses Python standard library only; not identical to local NumPy plotter.
"""
from math import sqrt, pi
PHI=(1+sqrt(5))/2
GE,GL,GI=.04,.04,.02
G=GE+GL+GI
def capture(r,source,fcenter):
    fx=fcenter/sqrt(r)
    fy=fcenter*sqrt(r)
    total=0.
    for f,w,mode in source:
        fr=fx if mode==0 else fy
        total+=w*4*GE*GL/(G*G+(fr-f)**2)
    return total

def scan(source):
    center=sqrt(source[0][0]*source[-1][0])
    candidates=[1+.0025*n for n in range(461)]
    best=max(((capture(r,source,center),r) for r in candidates))
    return (best[1],best[0],capture(PHI,source,center))

def load_eff(load):
    return 4*GE*load/(GE+load+GI)**2

def test():
    sets=[([(1,.5,0),(PHI,.5,1)],PHI),
          ([(1,.5,0),(1.3,.5,1)],1.3),
          ([(1,.5,0),(1.9,.5,1)],1.9)]
    for source,target in sets:
        r,amount,golden=scan(source)
        assert abs(r-target)<.01
        assert 0<=golden<=amount+.0001<=1+.0001
    assert load_eff(.06)>load_eff(.02)
    assert load_eff(.06)>load_eff(.16)
    assert abs(capture(PHI,sets[0][0],sqrt(PHI))-.64)<1e-10
    # Equal source spectra and mode capture never create new power:
    for r in [1,1.3,PHI,1.9]:
        for source,_ in sets:assert capture(r,source,sqrt(source[-1][0]))<=1
    print('PASS: 7 passive two-mode source/geometry tests')
    for source,_ in sets:print('spectrum:',source[-1][0],'best / golden:',scan(source))
if __name__=='__main__':test()
