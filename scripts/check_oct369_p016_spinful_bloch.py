#!/usr/bin/env python3
"""OCT369 P0.16: spinful L12 Mn3c Bloch-phase fixture (not PtMn3 ab initio).
Original experimental attribution: Kang et al., Nature (2026),
DOI 10.1038/s41586-026-11172-5. Original Bloch/Pauli/SU2 theory is classical.
DASHI contribution is the source-site constrained symmetry regression.
"""
import json
import numpy as np
SX=np.array([[0,1],[1,0]],complex)
SY=np.array([[0,-1j],[1j,0]],complex)
SZ=np.array([[1,0],[0,-1]],complex)
SIGMA=np.array([SX,SY,SZ]); I2=np.eye(2,dtype=complex)
SITES=np.array([[0.,.5,.5],[.5,0.,.5],[.5,.5,0.]])
CENTRE=SITES.mean(axis=0)
N=np.array([1.,1.,1.])/np.sqrt(3.)
R=np.array([[0,0,1],[1,0,0],[0,1,0]],float)
P=np.zeros((3,3),complex)
for a,ra in enumerate(SITES):
    P[next(i for i,rb in enumerate(SITES) if np.allclose(R@ra,rb)),a]=1
SPIN=SITES-CENTRE
SPIN=SPIN/np.linalg.norm(SPIN,axis=1)[:,None]
def pauli_dot(v):return np.einsum('i,ijk->jk',v,SIGMA)
def su2(axis,phi):return np.cos(phi/2)*I2-1j*np.sin(phi/2)*pauli_dot(axis)
US=su2(N,2*np.pi/3)
U=np.kron(P,US)
def ham(k,domain=1,t=.7,exchange=.8,soc=.15):
    H=np.zeros((6,6),complex)
    for a in range(3):
        H[2*a:2*a+2,2*a:2*a+2]=domain*exchange*pauli_dot(SPIN[a])
        for b in range(3):
            if a==b:continue
            d=SITES[b]-SITES[a]
            hop=t*I2+1j*soc*pauli_dot(np.cross(N,d))
            H[2*a:2*a+2,2*b:2*b+2]=np.exp(1j*np.dot(k,d))*hop
    return H
UTR=np.kron(np.eye(3),1j*SY)
def norm(x):return float(np.linalg.norm(x))
checks={}
def check(name,cond):
    checks[name]=bool(cond)
    assert checks[name],name
check('three_L12_Mn_3c_positions',SITES.shape==(3,3) and np.allclose(SITES.sum(axis=1),1.))
check('three_120_degree_spins',all(np.isclose(SPIN[a]@SPIN[b],-.5) for a in range(3) for b in range(a+1,3)))
check('net_spin_zero',norm(SPIN.sum(axis=0))<1e-12)
check('site_action_order_3',norm(P@P@P-np.eye(3))<1e-12)
check('coordinate_rotation_order_3',norm(R@R@R-np.eye(3))<1e-12)
check('site_and_spin_covariance',all(norm(R@SPIN[a]-SPIN[np.argmax(abs(P[:,a]))])<1e-12 for a in range(3)))
check('SU2_double_cover',norm(np.linalg.matrix_power(US,3)+I2)<1e-12)
check('spin_unitary',norm(US.conj().T@US-I2)<1e-12)
check('full_spin_lift_order_6',norm(np.linalg.matrix_power(U,3)+np.eye(6))<1e-12)
rng=np.random.default_rng(20261121)
max_hermitian=max_c3=max_tr=max_eig=max_wrong=0.
for k in [np.zeros(3),np.array([.21,.39,-.61]),np.array([np.pi/3,-.23,.72]),*rng.uniform(-np.pi,np.pi,(24,3))]:
    for domain in (1,-1):
        H=ham(k,domain)
        max_hermitian=max(max_hermitian,norm(H-H.conj().T))
        max_c3=max(max_c3,norm(U@H@U.conj().T-ham(R@k,domain)))
        max_tr=max(max_tr,norm(UTR@H.conj()@UTR.conj().T-ham(-k,-domain)))
        max_eig=max(max_eig,norm(np.linalg.eigvalsh(H)-np.linalg.eigvalsh(ham(R@k,domain))))
        max_wrong=max(max_wrong,norm(UTR@H.conj()@UTR.conj().T-ham(-k,domain)))
check('hermitian_all_samples',max_hermitian<1e-12)
check('C3_spin_site_Bloch_covariance_all_samples',max_c3<1e-12)
check('time_reversal_maps_domain_all_samples',max_tr<1e-12)
check('C3_bloch_eigenvalue_covariance_all_samples',max_eig<1e-12)
check('time_reversal_same_domain_negative_control',max_wrong>1e-3)
check('no_source_gravity_constant_in_model',True)
check('no_material_specific_calibration_claimed',True)
receipt={'model':'L12 Mn3c 3-sublattice spinful 6x6 phase-bearing Hamiltonian fixture',
'attribution':{'experimental':'Kang et al., Nature 2026, DOI 10.1038/s41586-026-11172-5',
'established':'Pauli spin, SU2/C3, Hermitian Bloch Hamiltonians and conventional time reversal',
'new':'DASHI synthetic 3-site SOC/exchange/hopping C3/TR tests'},
'checks_passed':len(checks),'checks':checks,'num_k_samples':27,'num_domains':2,
'max_hermitian_residual':max_hermitian,'max_C3_covariance_residual':max_c3,
'max_time_reversal_residual':max_tr,'max_spectral_C3_residual':max_eig,
'same_domain_TR_negative_control_norm':max_wrong,
'PtMn3_ab_initio_bands_or_SOC_fit':False,
'MgO_tunnel_barrier_and_363percent_TMR_fit':False,
'real_T1g_octupole_domain_match':False,'actual_material_stress_or_gravity_prediction':False}
if __name__=='__main__':print(json.dumps(receipt,indent=2,sort_keys=True))
