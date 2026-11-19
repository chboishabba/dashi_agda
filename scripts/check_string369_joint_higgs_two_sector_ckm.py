#!/usr/bin/env python3
"""Two-sector CKM and joint Higgs loading BIDI acceptance.
Original owners: YukawaFromCarrier, CKMExactWitnesses, CarrierHiggsMassReceipt,
check_ckm_from_physical_mass_matrix.py, Filsinger loaded modal work.
Classical SVD, generalized eigenvalues and Schur complement.
The up off-diagonal entries are symbolic carrier data, not physical masses.
CMS HIG-26-010, 2026-11-02: 125.065 +/- 0.088 GeV.
"""
import numpy as np
from math import pi,sqrt
from pathlib import Path
import runpy
v=246.22
source=runpy.run_path(str(Path(__file__).with_name('check_ckm_from_physical_mass_matrix.py')))
Yd=source['full_yukawa_matrix']()
# Original canonical up diag(1,2,3); named optional carrier entries 1/5,1/25,1/5.
for name,Yu in [('diagonal',np.diag([1,2,3])),('symbolic-upper',np.array([[1,.2,.04],[0,2,.2],[0,0,3]]))]:
    for chart,D in [('original',Yd),('conditional down reversed',Yd[::-1,::-1])]:
        U,su,Vhu=np.linalg.svd(Yu); L,sd,Vhd=np.linalg.svd(D)
        assert np.allclose(U@np.diag(su)@Vhu,Yu)
        assert np.allclose(L@np.diag(sd)@Vhd,D)
        V=U[:,::-1].conj().T@L[:,::-1]
        assert np.allclose(V.conj().T@V,np.eye(3))
        J=np.imag(V[0,0]*V[1,1]*V[0,1].conjugate()*V[1,0].conjugate())
        print(name,chart,'up',su[::-1]*v/sqrt(2),'down',sd[::-1]*v/sqrt(2),'CKM',abs(V),'J',J)
# Down-only row reversal CHANGES relative weak basis; it is not a common
# basis change. Such a chart requires an independently proved intertwiner.
m0=(1+sqrt(5))/2*v/pi;m=125.065;delta=m0*m0-m*m
assert abs(delta-440.08410680361703)<1e-8
for f in [(1,0,0),(0,1,0),(0,0,1),(1/3,1/3,1/3)]:
    z=1+f[0]*delta/m**2;dl=-f[1]*delta/(2*v*v);M=500
    k=sqrt(f[2]*delta*(M*M-m*m))
    H=np.array([[m0*m0+2*dl*v*v,k],[k,M*M]])
    Z=np.diag([1/sqrt(z),1])
    poles=np.sqrt(np.linalg.eigvalsh(Z@H@Z))
    assert abs(poles[0]-m)<1e-10
    assert abs((z-1)*m*m-2*v*v*dl+k*k/(M*M-m*m)-delta)<1e-8
    print(f,z,dl,k,poles)
print('OPEN independent weak chart, physical up/down kinetic metrics, CY Hessian and pole self-energy')
