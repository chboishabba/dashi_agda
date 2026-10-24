#!/usr/bin/env python3
"""Gauge-sector coherence BIDI for ordinary charged Dirac fermions.

The even-parity vacuum/pair logical basis has charges (0,2); one-particle
dual-rail (10,01) has charges (1,1). Only the latter keeps unreferenced
coherence under ordinary global U(1). A superconducting condensate/charge
reservoir may provide a relational phase reference, but is NOT modeled.
"""
import numpy as np
I=np.eye(2,dtype=complex)
plus=np.ones(2,complex)/np.sqrt(2)
rho=np.outer(plus,plus.conj())
R_even=np.diag([1,-1]).astype(complex)
R_rail=-I
twirl_even=(rho+R_even@rho@R_even.conj().T)/2
twirl_rail=(rho+R_rail@rho@R_rail.conj().T)/2
assert np.allclose(twirl_even,I/2)
assert np.allclose(twirl_rail,rho)
assert abs(np.trace(twirl_even@twirl_even)-.5)<1e-12
assert abs(np.trace(twirl_rail@twirl_rail)-1)<1e-12
for theta in np.linspace(0,2*np.pi,41):
    U=np.diag([1,np.exp(2j*theta)])
    V=np.exp(1j*theta)*I
    assert np.allclose(U@twirl_even@U.conj().T,twirl_even)
    assert np.allclose(V@rho@V.conj().T,rho)
print('PASS: undressed charge-0/2 parity coherence removed by U1 sector twirl')
print('PASS: charge-1/1 dual-rail coherence survives common U1 phase')
print('OPEN: actual physical MMP charge-dressed state or superconducting phase reference')
