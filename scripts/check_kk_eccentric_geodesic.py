#!/usr/bin/env python3
"""High-precision eccentric geodesic time-average for boosted Kerr KK static metric.
First order in physical J; fixed coordinate radial turning points. No Earth matching.
"""
import mpmath as m
import numpy as np
m.mp.dps=60
nodes,weights=np.polynomial.legendre.leggauss(80)
M=m.mpf('3.986004418e14')/m.mpf('299792458')**2
def average(a,e,alpha):
    a=m.mpf(str(a));e=m.mpf(str(e));alpha=m.mpf(str(alpha));q=m.sinh(alpha)**2
    rp=a*(1-e);ra=a*(1+e)
    def A(r):return (1-2*M/r)/m.sqrt(1+2*M*q/r)
    def B(r):return m.sqrt(1+2*M*q/r)/(1-2*M/r)
    def C(r):return r*r*m.sqrt(1+2*M*q/r)
    ap,aa=A(rp),A(ra);cp,ca=C(rp),C(ra)
    L2=(aa-ap)/(ap/cp-aa/ca);E2=ap*(1+L2/cp)
    assert L2>0 and E2>0
    d=n=m.mpf(0)
    for node,weight in zip(nodes,weights):
        chi=(m.mpf(str(node))+1)*m.pi/4
        w=m.mpf(str(weight))*m.pi/4
        r=rp+(ra-rp)*m.sin(chi)**2
        dr=2*(ra-rp)*m.sin(chi)*m.cos(chi)
        rad=E2/A(r)-1-L2/C(r)
        assert rad>0
        dt=m.sqrt(E2)/A(r)*m.sqrt(B(r)/rad)*dr
        d+=w*dt
        n+=w*dt/(r**3*(1+2*M*q/r))
    return n/d
if __name__=='__main__':
    for a,e in ((7820e3,.001),(12270e3,.0045)):
        base=average(a,e,0)
        for alpha in (0,.3,1):
            value=average(a,e,alpha)
            print(f'a={a/1000:g}km e={e} alpha={alpha} delta={float(value/base-1):+.9e}')
            if alpha==0:assert abs(value/base-1)<m.mpf('1e-48')
    print('PASS high-precision eccentric KK geodesic average')
