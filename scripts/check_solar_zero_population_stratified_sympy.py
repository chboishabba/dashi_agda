"""Exact stratified-support obstruction and smooth amplitude exchange weld.

The native padded material generator sets collision and gyro blocks to zero
for D=0 but activates them for every D>0. Hence the full zero-density JVP
cannot be obtained from the smooth sqrt(D) Whitney coupling alone.
"""
import sympy as s
q,nu,g,w,V,m=s.symbols('q nu g w V m',positive=True)
# A species block on one field coordinate and two current coordinates.
Aplus=s.Matrix([[0,-w*q/s.sqrt(V*m),0],
                [w*q/s.sqrt(V*m),-nu,g],
                [0,-g,-nu]])
Azero=s.zeros(3)
dexchange=s.diff(Aplus,q)
assert dexchange.subs(q,0)==s.Matrix([[0,-w/s.sqrt(V*m),0],
                                    [w/s.sqrt(V*m),0,0],[0,0,0]])
limit=Aplus.subs(q,0)
jump=limit-Azero
assert jump==s.Matrix([[0,0,0],[0,-nu,g],[0,-g,-nu]])
assert jump!=s.zeros(3)
# Operator discontinuity: (A(q)-A(0))/q diverges for nonzero nu or g.
assert s.simplify(s.diff((Aplus[1,1]-Azero[1,1])/q,q))==nu/q**2
# Restricting all current state coordinates to zero makes the field source
# coupling vanish exactly at q=0; a new support chart is still required.
z=s.symbols('z',real=True)
assert (Azero*s.Matrix([z,0,0]))==s.zeros(3,1)
# Smooth exchange has a finite one-sided q derivative, but D=q^2 has
# singular d/dD coupling as D -> 0.
D=s.symbols('D',positive=True)
cd=w*s.sqrt(D)/s.sqrt(V*m)
assert s.limit(s.diff(cd,D),D,0,dir='+')==s.oo
print(dict(status='PASS',exchange_amplitude_jvp=True,
           native_full_generator_discontinuous=True,
           zero_support_full_jvp_admitted=False))
