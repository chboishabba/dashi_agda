"""Exact rational exterior certificate for original far shrinking observation.
Uses the original causal RK3 rational bound helpers. No numerical null claim.
"""
from fractions import Fraction as F
from check_f8_causal_rk3_weld import sqrt_bounds, log_bounds


def elapsed(t, s):
    a,b=sqrt_bounds(F(1+t*t));c,d=sqrt_bounds(F(1+s*s))
    return (log_bounds((t+a)/(s+d))[0]-b/t+c/s,
            log_bounds((t+b)/(s+c))[1]-a/t+d/s)


def exterior(delta,dr,dy,dt):
    delta,dr,dy,dt=map(lambda x:F(str(x)),(delta,dr,dy,dt))
    if min(delta,dr,dy,dt)<=0:raise ValueError('positive patch geometry')
    lo,hi=elapsed(12,1)
    bulk=sqrt_bounds(lo*lo-F(11,12)**2)[0]
    # Nonzero coefficients of each first/second or mixed derivative extend
    # the compact patch by at most one node in each coordinate.
    earliest=F(3,2)*delta+dt
    late=elapsed(12,10)[0]>earliest
    # |b_T| <= 1/10 on t>=10; otherwise use the global bound 3/4.
    zmax=F(1,12)+2*delta+dy+(F(1,10) if late else F(3,4))*earliest
    rmin=bulk+F(1,10)-delta/2-dr-F(1,25)
    Tmax=hi-delta/2+dt
    if rmin<=0 or Tmax<=0:raise ValueError('outside certificate geometry')
    dist=sqrt_bounds(rmin*rmin+max(F(0),1-zmax)**2)[0]
    return dict(certified_exterior=dist>Tmax,margin_lower=float(dist-Tmax),late_clock=late,
                resolved=delta>=4*max(dr,dy,dt))


def check():
    rows=[]
    for dr,dy in ((.008,.012),(.006,.009)):
        for delta in (.048,.05,.06,.09,.18):
            r=exterior(delta,dr,dy,.0006)
            if delta<=.06:assert r['certified_exterior'] and r['resolved']
            if delta>=.09:assert not r['certified_exterior']
            rows.append(dict(dr=dr,dy=dy,delta=delta,**r))
    return rows


if __name__=='__main__':print(check())
