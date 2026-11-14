#!/usr/bin/env python3
"""Single-coherent-wave nonlinear two-mode model, fixed golden ratio.
Requires NumPy and SciPy. Not a full Maxwell antenna or a measured device.
No CI dependency. Mirrors the independently locally tested source model.
"""
from math import sqrt
import unittest
import numpy as np
from scipy.integrate import solve_ivp
PHI=(1+sqrt(5))/2
ge,gi,gl=.04,.02,.04
g=ge+gi+gl
source=sqrt(ge)*np.array([1.+0j,1.+0j]) # 45° ONE incident wave

def derivative(a,tx,ty,k,chi,mu,driven=True):
    det=np.array([tx/sqrt(PHI)-1,ty*sqrt(PHI)-1])
    fwm=np.array([np.conj(a[0])*a[1]**2,np.conj(a[1])*a[0]**2])
    return (-g*a + 1j*(det*a+k*a[::-1]+chi*np.abs(a)**2*a+mu*fwm)
            + (source if driven else 0))

def solve(tx=1.,ty=1.,k=0.,chi=0.,mu=0.):
    def real_rhs(t,y):
        a=y[:2]+1j*y[2:]
        da=derivative(a,tx,ty,k,chi,mu)
        return np.r_[da.real,da.imag]
    r=solve_ivp(real_rhs,(0,550),np.zeros(4),method="DOP853",rtol=2e-8,atol=1e-10)
    a=r.y[:2,-1]+1j*r.y[2:,-1]
    u=np.vdot(a,a).real
    return {"useful":2*gl*u,"circularity":2*np.imag(np.conj(a[0])*a[1])/u,
            "input_work":2*np.real(np.vdot(a,source)), "residual":2*np.real(np.vdot(a,source))-2*g*u}

class GateChecks(unittest.TestCase):
    def test_original_phi(self):self.assertAlmostEqual(PHI**2,PHI+1)
    def test_one_source(self):self.assertAlmostEqual(np.vdot(source,source).real,2*ge)
    def test_four_wave_mixing_conservative(self):
        a=np.array([.6+.2j,-.8+1.4j])
        fwm=np.array([np.conj(a[0])*a[1]**2,np.conj(a[1])*a[0]**2])
        self.assertAlmostEqual(np.vdot(a,1j*.1*fwm).real,0)
    def test_coupling_and_kerr_conservative(self):
        a=np.array([.4+.2j,1.+.7j])
        coupling=1j*.05*a[::-1]+1j*.2*np.abs(a)**2*a
        self.assertAlmostEqual(np.vdot(a,coupling).real,0)
    def test_source_off_decay(self):
        a=np.array([.2+.6j,-.7+1j])
        d=derivative(a,1.1,.95,.03,.04,-.03,False)
        self.assertAlmostEqual(2*np.vdot(a,d).real,-2*g*np.vdot(a,a).real)
    def test_normalized_power_and_budget(self):
        for v in [(1.,1.,0.,0.,0.),(.91,.98,.02,.01,.03),(1.15,.9,.05,.04,-.04)]:
            x=solve(*v)
            self.assertLessEqual(x["useful"],1.00001)
            self.assertLess(abs(x["residual"]),1e-5)
    def test_quadrature_not_automatic(self):
        self.assertLess(abs(solve()["circularity"]),.999)

if __name__=="__main__":unittest.main(verbosity=2)
