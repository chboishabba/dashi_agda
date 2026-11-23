"""LXXXIX F8 P0: reverse-solve the ORIGINAL physical near-photon guard.

No surrogate PDE, no CI. Exact SymPy identities for original F' and Q',
then independent bracketed roots of the weak-source guard (not physical
wave-arrival observations). Source outer support .048 in both original
A1/C1 weak-load grids, t=12 physical receiver.
"""
import json
import sympy as sp
from scipy.optimize import brentq

t=sp.symbols('t',positive=True)
F=sp.asinh(t)-sp.sqrt(1+t*t)/t
F1=F.subs(t,1)
Fprime=sp.diff(F,t)
assert sp.simplify(Fprime-sp.sqrt(1+t*t)/t**2)==0
Q=(F-F1)**2-(1-1/t)**2
qprime=2*(F-F1)*Fprime-2*(1-1/t)/t**2
assert sp.simplify(sp.diff(Q,t)-qprime)==0
bulk=sp.sqrt(Q)
receiver=bulk-sp.Rational(12,1000)
source_last_plus_dr=sp.Rational(48,1000)
def guard(dr):
    return receiver-sp.log(t)-source_last_plus_dr-dr/2
results={}
for name,dr in [('A1',sp.Rational(8,1000)),('C1',sp.Rational(6,1000))]:
    g=sp.simplify(guard(dr))
    gg=sp.lambdify(t,g,'numpy')
    root=brentq(gg,10.,12.,xtol=5e-14)
    margin=float(g.subs(t,12).evalf(45))
    slope=float(sp.diff(g,t).subs(t,12).evalf(45))
    assert abs(float(gg(root)))<1e-12 and margin>0
    assert float(gg(root-sp.Rational(1,100)))<0
    assert float(gg(root+sp.Rational(1,100)))>0
    results[name]=dict(radial_spacing=float(dr),threshold_t=root,
        margin_at_12=margin,margin_slope_at_12=slope,
        source_outer_edge=float(source_last_plus_dr),
        near_receiver_r_at_12=float(receiver.subs(t,12).evalf(45)))
assert sp.simplify(guard(sp.Rational(6,1000))-guard(sp.Rational(8,1000))
                   -sp.Rational(1,1000))==0
assert results['C1']['threshold_t']<results['A1']['threshold_t']<12
print(json.dumps(dict(status='PASS',Fprime=str(Fprime),
    source='original master/#1527 production F, bulk, receiver and weak hat guard',
    results=results,
    limits='Geometry-only inverse guard: not full native propagation, physical arrival, 96-output receiver or convergence'),indent=2))
