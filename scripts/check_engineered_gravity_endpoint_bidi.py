"""Endpoint-first engineered gravity benchmark, not a new gravity model.
SI rational arithmetic and symbolic weak-field discriminators.  No empirical
promotion, no claim that a prescribed metric is a realizable device.
"""
import sympy as s
from fractions import Fraction as F

G=F("6.67430e-11")
C=299792458
G0=F("9.80665")

def monopole(g,r,m):
    g,r,m=map(F,(g,r,m))
    if min(g,r,m)<=0: raise ValueError("positive target, distance, mass")
    mass=g*r*r/G
    return dict(active_mass=mass, gain=mass/m, equivalent_energy=mass*C*C,
                metric_gradient=2*g/C**2, radial_tidal=2*g/r)

def shielding(before,after):
    """Same source, reference frame and isolated gravity-channel receiver.
    Scalar signed collinear case only; not inferred from apparent weight."""
    before,after=map(F,(before,after))
    if before==0: raise ValueError("nonzero baseline required")
    return 1-after/before

def exact():
    x,y,z=s.symbols("x y z", real=True)
    g,L=s.symbols("g L", positive=True)
    # Two local potentials agree on acceleration at origin but not tides.
    p=g*x
    q=g*x+g*x*x/(2*L)
    coords=(x,y,z)
    accel=lambda p:-s.Matrix([s.diff(p,i) for i in coords])
    tide=lambda p:-s.hessian(p,coords)
    assert accel(p)==accel(q).subs(x,0)
    assert tide(p)==s.zeros(3) and tide(q)[0,0]==-g/L
    # Uniform coordinate gravity alone cannot distinguish an accelerated lab.
    # Exact Rindler metric in c=1 units: lapse 1+a*x, curvature vanishes.
    a=s.symbols("a",real=True)
    N=1+a*x
    assert s.diff(N,x,2)==0
    # Active source in stationary linearized GR: epsilon+sum pressures,
    # not Lorentz trace -epsilon+sum pressures.
    e,p1,p2,p3=s.symbols("e p1 p2 p3",real=True)
    trace=-e+p1+p2+p3
    active=e+p1+p2+p3
    assert s.expand(active-trace)==2*e
    assert trace.subs({e:1,p1:0,p2:0,p3:0})<0
    assert active.subs({e:1,p1:0,p2:0,p3:0})>0
    # Exact conventional Newtonian point-source benchmark.
    b=monopole(G0,1,1000)
    assert b["gain"]>10**8
    assert b["active_mass"]*G==G0
    assert shielding(1,1)==0 and shielding(1,0)==1
    assert shielding(1,-1)==2
    # Counterforce gives zero load but does not change gravity channel.
    gravity,em=s.symbols("gravity em")
    assert (gravity+em).subs(em,-gravity)==0
    assert shielding(1,1)==0
    # Radion-only flat induced brane: changing circle radius is insufficient.
    phi=s.Function("phi")(x)
    metric=s.diag(-1,1,1,1,phi**2)
    assert metric[:4,:4]==s.diag(-1,1,1,1)
    assert all(s.diff(metric[0,0],v)==0 for v in coords)
    for key,val in b.items(): print(key,format(float(val),".9e"))
    print("PASS conditional benchmark identities; no source or device certified")

if __name__=="__main__": exact()
