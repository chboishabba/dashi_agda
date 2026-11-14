#!/usr/bin/env python3
"""Exact 2-D rectangular PEC TMz cavity mode Maxwell benchmark, source-aware.
Not the actual external Smith/Filsinger metal plate. phasor exp(-i wt).
mu=eps=1. Faraday curl E = i*w*mu*H;
Ampere curl H = J-i*w*eps*E.
"""
from math import pi,sqrt,sin,cos
import unittest
PHI=(1+sqrt(5))/2
def mode(m,n,x,y,a=PHI,b=1.,omega=None,mu=1.,eps=1.):
    kx=m*pi/a;ky=n*pi/b;k2=kx*kx+ky*ky
    eigen=sqrt(k2/(mu*eps))
    if omega is None:omega=eigen
    e=sin(kx*x)*sin(ky*y)
    ex=kx*cos(kx*x)*sin(ky*y)
    ey=ky*sin(kx*x)*cos(ky*y)
    hx=ey/(1j*omega*mu);hy=-ex/(1j*omega*mu)
    curlh=k2*e/(1j*omega*mu)
    j=-1j*(k2-omega*omega*mu*eps)/(omega*mu)*e
    return dict(e=e,hx=hx,hy=hy,j=j,omega=omega,eigen=eigen,
        faraday=abs(ey-1j*omega*mu*hx)+abs(-ex-1j*omega*mu*hy),
        ampere=abs(curlh-(j-1j*omega*eps*e)))
class Tests(unittest.TestCase):
    def test_boundary(self):
        for x,y in [(0,.2),(PHI,.5),(.3,0),(.2,1)]:
            self.assertAlmostEqual(mode(1,2,x,y)['e'],0,places=10)
    def test_faraday_and_ampere(self):
        for m,n in [(1,2),(2,1)]:
            s=mode(m,n,.43,.24)
            self.assertLess(s['faraday'],1e-10)
            self.assertLess(s['ampere'],1e-10)
            self.assertAlmostEqual(abs(s['j']),0)
    def test_distinct_actual_mode_ratio(self):
        x=mode(1,2,.43,.24)['omega'];y=mode(2,1,.43,.24)['omega']
        self.assertAlmostEqual(max(x,y)/min(x,y),1.3166115054373,places=10)
    def test_common_drive_needs_source_or_loading(self):
        x=mode(1,2,.43,.24)['omega'];y=mode(2,1,.43,.24)['omega'];w=(x+y)/2
        for m,n in [(1,2),(2,1)]:
            s=mode(m,n,.43,.24,omega=w)
            self.assertGreater(abs(s['j']),.01)
            self.assertLess(s['ampere'],1e-10)
if __name__=="__main__":unittest.main(verbosity=2)
