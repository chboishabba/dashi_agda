#!/usr/bin/env python3
"""Original FN and SI/atomic/CMS donor audit, not physical CY prediction."""
import numpy as np
from pathlib import Path
import runpy
v=246.22
Y=runpy.run_path(str(Path(__file__).with_name('check_ckm_from_physical_mass_matrix.py')))['full_yukawa_matrix']()
U=np.array([[1,.2,.04],[0,2,.2],[0,0,3.]])
e=.225
D=np.diag([e**3,e**2,1])
for name,C in [('original',Y),('conditional reversed',Y[::-1,::-1])]:
    A=D@U@D; B=D@C@D
    L,x,_=np.linalg.svd(A); R,y,_=np.linalg.svd(B)
    V=L[:,::-1].conj().T@R[:,::-1]
    assert np.allclose(V.conj().T@V,np.eye(3))
    mu=x[::-1]*172.5/x[0]; md=y[::-1]*4.18/y[0]
    assert np.allclose(mu,[.00745848293,.294803700,172.5])
    print(name,mu,md,abs(V))
# SI conversion is common scaling, cannot change mass ratios.
# Common unitary Fourier basis change cannot change CKM or singular values.
F=np.exp(2j*np.pi*np.outer(np.arange(3),np.arange(3))/3)/np.sqrt(3)
A=D@U@D
assert np.allclose(np.linalg.svd(F@A@F.conj().T,compute_uv=False),np.linalg.svd(A,compute_uv=False))
# A single shared left metric alone imposes a fixed generalized spectrum:
# det(Hu-lambda Hd)=0 unchanged by simultaneous invertible congruence.
# Thus independent right metrics or interaction changes may be necessary.
for C in (Y,Y[::-1,::-1]):
    B=D@C@D
    Hu=A@A.conj().T; Hd=B@B.conj().T
    # determinant ratio test for any common normalization, allowing
    # separate overall sector scales; compare normalized eigenvalue shapes.
    eig=np.linalg.eigvals(np.linalg.solve(Hd,Hu))
    print('generalized spectrum',np.sort(eig.real))
print('OPEN actual common-source CY overlap and kinetic metrics, RG matching and held-out CMS prediction')
