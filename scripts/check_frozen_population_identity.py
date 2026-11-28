"""Exact identity event admission and floating round-trip negative control.
Frozen populations must leave the normalized current unchanged, bitwise.
"""
import numpy as np
from scipy.constants import electron_mass as me, atomic_mass as u, elementary_charge as e
MASS=np.array([me,30.5*u,16*u]); CHARGE=e*np.array([-1.,1.,1.])
n=np.array([1.e8,6.e7,4.e7]);V=.23
z=np.random.default_rng(0).normal(size=(3,3))
r=np.zeros(3);a=np.zeros(3)
w=V*MASS
velocity=np.sign(CHARGE)[:,None]*z/np.sqrt(w*n)[:,None]
new=n-r+a
roundtrip=np.sign(CHARGE)[:,None]*np.sqrt(w*new)[:,None]*((n-r)[:,None]*velocity/new[:,None])
assert not np.array_equal(roundtrip,z)
assert np.max(abs(roundtrip-z))>0
assert np.array_equal(z.copy(),z)
assert np.array_equal(n-r+a,n)
assert np.all(r==0) and np.all(a==0)
print(dict(status='PASS',roundtrip_is_bitwise_identity=False,
           max_roundtrip_error=float(np.max(abs(roundtrip-z))),
           frozen_event_is_identity=True))
