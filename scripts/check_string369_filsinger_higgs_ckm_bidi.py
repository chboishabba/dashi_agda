#!/usr/bin/env python3
"""BIDI Higgs pole and CKM handedness audit.
Classical: generalized Hermitian eigenproblem, Schur complement, SVD.
Original DASHI CarrierHiggsMassReceipt, check_ckm_from_physical_mass_matrix,
SmithFilsingerReflectionMaxwellPortCut20261112 and golden rectangle work.
Not a derived CY kinetic metric or pole self-energy. Benchmark 125.065
is inherited from previous PR, not independently verified here.
"""
import numpy as np
import sympy as s
from math import pi,sqrt
v=246.22; target=125.065; bare=(1+sqrt(5))/2*v/pi
Z=(bare/target)**2
delta=bare**2-target**2
print('required Z-1',Z-1,'required mass-square lowering',delta)
# Positive heavy-mode elimination gives a downward shift of the light pole.
a,b,c,t=s.symbols('a b c t',real=True)
M=s.Matrix([[a,b],[b,c]])
assert s.expand((M-t*s.eye(2)).det()-(c-t)*(a-t)+b*b)==0
# If c>t and a>t then b²=(a-t)(c-t). Family of inverse solutions,
# not uniquely determined mixing or an independent explanation.
# Golden geometric overlap is not the dimensionless physical loading.
# Explicit source texture copied from original numerical diagnostic.
alpha=.041240; phase=np.angle((1+2j*sqrt(7))/(5+2j))
Y=np.array([[alpha*2*pi,alpha*pi*sqrt(3),alpha**3*24*pi/sqrt(6)*np.exp(1j*phase)],[0,alpha**2*4*pi/3,alpha**2*14/sqrt(24)*8*pi/3],[0,0,alpha**3*8*pi/3]])
U,d,Vh=np.linalg.svd(Y)
assert np.allclose(U@np.diag(d)@Vh,Y)
assert np.allclose(Y@Y.conj().T,U@np.diag(d*d)@U.conj().T)
assert np.allclose(Y.conj().T@Y,Vh.conj().T@np.diag(d*d)@Vh)
left=abs(U[::-1,::-1]);right=abs(Vh.conj().T[:,::-1])
print('left benchmark (assumed up identity, reversed ordering)',left)
print('original right diagnostic',right)
print('masses',d[::-1]*v/sqrt(2))
assert abs(left[2,2]-.999898835)<1e-6
print('OPEN source weak-current basis, up rotation, CY kinetic and potential Hessians, independent pole correction')
