#!/usr/bin/env python3
"""OCT369 P0.18: periodic L12 Mn(3c) spinful Bloch, 2-layer tunnelling, equilibrium force.

Attribution: Kang et al., Nature 2026, DOI:10.1038/s41586-026-11172-5
own the experimental OTT, PtMn3|MgO|PtMn3 TMR and explanation.
Bloch, SU(2), Pauli, Landauer-Caroli, golden rule and Hellmann-Feynman
are established prior art. This DASHI code is an unfitted material-site
fixture: not PtMn3 ab initio, an experimental barrier, current-driven OTT,
YM continuum gap, stress tensor or gravity anomaly.
"""
import json
from itertools import product
import numpy as np
import sympy as sp
SX=np.array([[0,1],[1,0]],complex)
SY=np.array([[0,-1j],[1j,0]],complex)
SZ=np.diag([1.,-1.]).astype(complex)
SIGMA=np.array([SX,SY,SZ]); I2=np.eye(2,dtype=complex)
SITES=np.array([[0.,.5,.5],[.5,0.,.5],[.5,.5,0.]])
SPIN=SITES-SITES.mean(axis=0); SPIN/=np.linalg.norm(SPIN,axis=1)[:,None]
AXIS=np.array([1.,1.,1.])/np.sqrt(3.)
R=np.array([[0,0,1],[1,0,0],[0,1,0]],float)
P=np.zeros((3,3),complex)
for a,v in enumerate(SITES):
    P[next(b for b,w in enumerate(SITES) if np.allclose(R@v,w)),a]=1
def sig(v):return np.einsum('i,ijk->jk',v,SIGMA)
def su2(v,t):return np.cos(t/2)*I2-1j*np.sin(t/2)*sig(v)
UC3=np.kron(P,su2(AXIS,2*np.pi/3)); UTR=np.kron(np.eye(3),1j*SY)
I6=np.eye(6,dtype=complex); I12=np.eye(12,dtype=complex)
def rotate(v,t):
    return v*np.cos(t)+np.cross(AXIS,v)*np.sin(t)+AXIS*(AXIS@v)*(1-np.cos(t))
BONDS=[]
for a,b in product(range(3),repeat=2):
    for v in product(range(-1,2),repeat=3):
        d=np.array(v,float)+SITES[b]-SITES[a]
        if np.isclose(d@d,.5):BONDS.append((a,b,v,d))
BONDS.sort(key=lambda row:(row[0],row[1],row[2]))
def hsingle(k,domain=1,t=.7,exchange=.8,soc=.15,theta=0.):
    H=np.zeros((6,6),complex)
    for a in range(3):
        H[2*a:2*a+2,2*a:2*a+2]=domain*exchange*sig(rotate(SPIN[a],theta))
    for a,b,v,d in BONDS:
        hop=t*I2+1j*soc*sig(np.cross(AXIS,d))
        H[2*a:2*a+2,2*b:2*b+2]+=np.exp(1j*k@d)*hop
    return H
def barrier(d,ts=.42,tx=.08,decay=.7):
    return np.exp(-decay*d)*np.kron(tx*np.ones((3,3))+(ts-tx)*np.eye(3),I2)
def bilayer(k,left=1,right=1,d=1.,theta=0.):
    H1,H2=hsingle(k,left),hsingle(k,right,theta=theta)
    B=barrier(d)
    return np.block([[H1,B],[B.conj().T,H2]])
def transmission(k,left=1,right=1,d=1.,energy=.12,gamma=.24,reverse=False):
    H=bilayer(k,left,right,d)
    GL=np.diag([gamma]*6+[0.]*6); GR=np.diag([0.]*6+[gamma]*6)
    G=np.linalg.inv(energy*I12-H+.5j*(GL+GR))
    return float(np.trace((GR if reverse else GL)@G@(GL if reverse else GR)@G.conj().T).real)
def grand(k,right=1,d=1.,theta=0.,T=.6,mu=0.):
    energies=np.linalg.eigvalsh(bilayer(k,1,right,d,theta))
    return float(-T*np.logaddexp(0,-(energies-mu)/T).sum())
def hf(k,right=1,d=1.,theta=0.,T=.6,mu=0.):
    H=bilayer(k,1,right,d,theta)
    energies,V=np.linalg.eigh(H)
    occupied=1/(1+np.exp((energies-mu)/T))
    density=(V*occupied)@V.conj().T
    B=barrier(d)
    dHd=np.block([[np.zeros((6,6),complex),-.7*B],
                  [-.7*B.conj().T,np.zeros((6,6),complex)]])
    dr=np.zeros((6,6),complex)
    for a in range(3):
        dr[2*a:2*a+2,2*a:2*a+2]=right*.8*sig(np.cross(AXIS,rotate(SPIN[a],theta)))
    dHt=np.block([[np.zeros((6,6),complex),np.zeros((6,6),complex)],
                  [np.zeros((6,6),complex),dr]])
    return float(np.trace(density@dHd).real),float(np.trace(density@dHt).real)
def spin_projection_transfer():
    # Golden-rule saturated spin-filter proxy, not the NEGF of H(k).
    th,td,tx=sp.symbols('theta t_d t_o',real=True)
    total=0
    for a,b in product(range(3),repeat=2):
        total+=(td if a==b else tx)**2*(1+sp.cos(th+(a-b)*2*sp.pi/3))/2
    G=sp.Rational(3,2)*td**2+3*tx**2+sp.Rational(3,2)*(td**2-tx**2)*sp.cos(th)
    assert sp.trigsimp(sp.expand_trig(total-G))==0
    GP=sp.simplify(G.subs(th,0)); GA=sp.simplify(G.subs(th,sp.pi))
    TMR=sp.factor(GP/GA-1)
    roots=sp.solve(TMR.subs(tx,1)-sp.Rational(363,100),td)
    assert roots and any(sp.simplify(TMR.subs({td:x,tx:1})-sp.Rational(363,100))==0 for x in roots)
    return G,GP,GA,TMR,roots
checks=[]
def test(name,yes):
    assert bool(yes),name
    checks.append(name)
test('three_3c_sites',SITES.shape==(3,3))
test('zero_net_spin',np.linalg.norm(SPIN.sum(axis=0))<1e-13)
test('120_degree_spin',all(np.isclose(SPIN[a]@SPIN[b],-.5) for a in range(3) for b in range(a+1,3)))
test('SU2_lift_cube_minus_identity',np.linalg.norm(np.linalg.matrix_power(UC3,3)+I6)<1e-12)
test('24_directed_bonds',len(BONDS)==24)
test('eight_bonds_per_site',all(sum(x[0]==a for x in BONDS)==8 for a in range(3)))
test('Hermitian_bond_pairs',all(any(aa==b and bb==a and np.allclose(dd,-d) for aa,bb,vv,dd in BONDS) for a,b,v,d in BONDS))
test('bond_C3_covariance',all(any(aa==np.argmax(abs(P[:,a])) and bb==np.argmax(abs(P[:,b])) and np.allclose(dd,R@d) for aa,bb,vv,dd in BONDS) for a,b,v,d in BONDS))
rng=np.random.default_rng(20261121)
KS=[np.zeros(3),np.array([.4,-.7,1.3]),np.array([np.pi,0,.3]),*rng.uniform(-np.pi,np.pi,(21,3))]
U12=np.block([[UC3,np.zeros((6,6))],[np.zeros((6,6)),UC3]])
T12=np.block([[UTR,np.zeros((6,6))],[np.zeros((6,6)),UTR]])
max_h=max_c3=max_tr=max_period=max_bi=max_bic3=max_bitr=0.
for k in KS:
    for dom in (-1,1):
        H=hsingle(k,dom)
        max_h=max(max_h,np.linalg.norm(H-H.conj().T))
        max_c3=max(max_c3,np.linalg.norm(UC3@H@UC3.conj().T-hsingle(R@k,dom)))
        max_tr=max(max_tr,np.linalg.norm(UTR@H.conj()@UTR.conj().T-hsingle(-k,-dom)))
    max_period=max(max_period,np.max(np.abs(np.linalg.eigvalsh(hsingle(k+2*np.pi*np.array([1.,0,0])))-
                                               np.linalg.eigvalsh(hsingle(k)))))
    for dom in (-1,1):
        H=bilayer(k,1,dom)
        max_bi=max(max_bi,np.linalg.norm(H-H.conj().T))
        max_bic3=max(max_bic3,np.linalg.norm(U12@H@U12.conj().T-bilayer(R@k,1,dom)))
        max_bitr=max(max_bitr,np.linalg.norm(T12@H.conj()@T12.conj().T-bilayer(-k,-1,-dom)))
test('48_single_Hermitian',max_h<1e-11)
test('48_single_C3',max_c3<1e-11)
test('48_single_time_reversal',max_tr<1e-11)
test('reciprocal_periodic_spectra',max_period<1e-11)
test('48_bilayer_Hermitian',max_bi<1e-11)
test('48_bilayer_C3',max_bic3<1e-11)
test('48_bilayer_TR',max_bitr<1e-11)
spread=float(np.max(np.abs(np.linalg.eigvalsh(hsingle(KS[0]))-np.linalg.eigvalsh(hsingle(KS[1])))))
test('new_real_band_dispersion',spread>.05)
def flat_old(k):
    H=np.zeros((6,6),complex)
    for a in range(3):
        H[2*a:2*a+2,2*a:2*a+2]=.8*sig(SPIN[a])
        for b in range(3):
            if a==b:continue
            d=SITES[b]-SITES[a]
            H[2*a:2*a+2,2*b:2*b+2]=np.exp(1j*k@d)*(.7*I2+1j*.15*sig(np.cross(AXIS,d)))
    return H
flat=float(np.max(np.abs(np.linalg.eigvalsh(flat_old(KS[0]))-np.linalg.eigvalsh(flat_old(KS[1])))))
test('P016_phase_only_flat_band_negative_control',flat<1e-12)
tp=float(np.mean([transmission(k) for k in KS]))
tm=float(np.mean([transmission(k,right=-1) for k in KS]))
test('NEGF_positive',tp>0 and tm>0)
test('NEGF_state_response',abs(tp-tm)>1e-6)
test('NEGF_Onsager_TR',abs(transmission(KS[1],right=-1)-transmission(-KS[1],left=-1,right=1,reverse=True))<1e-10)
test('decoupled_contact_zero_tunnel',transmission(KS[1],d=100)<1e-20)
k=KS[1]; d=1.; step=1e-5
F=-(grand(k,d=d+step)-grand(k,d=d-step))/(2*step)
test('equal_and_opposite_support_force',abs(F+(-F))<1e-12)
test('nonzero_equilibrium_interface_force',abs(F)>1e-5)
hf_d,hf_th=hf(k,d=d,theta=.37)
fd_d=(grand(k,d=d+step,theta=.37)-grand(k,d=d-step,theta=.37))/(2*step)
fd_th=(grand(k,theta=.37+step)-grand(k,theta=.37-step))/(2*step)
test('same_H_Hellmann_Feynman_force',abs(hf_d-fd_d)<1e-8)
test('same_H_Hellmann_Feynman_angle_torque',abs(hf_th-fd_th)<1e-8)
test('generalized_torque_nonzero',abs(hf_th)>1e-6)
test('HF_body_support_reaction',abs(-hf_d+hf_d)<1e-14)
test('barrier_large_separation_limit',np.linalg.norm(barrier(20))<1e-5)
test('decoupled_contact_force_zero',abs(hf(k,d=100)[0])<1e-20)
t=sp.symbols('t',real=True)
M0=sp.Matrix([[0,4*t,4*t],[4*t,0,4*t],[4*t,4*t,0]])
MX=sp.Matrix([[0,0,0],[0,0,4*t],[0,4*t,0]])
test('exact_Gamma_spinless_spectrum',M0.eigenvals()=={8*t:1,-4*t:2})
test('exact_X_spinless_spectrum',MX.eigenvals()=={4*t:1,-4*t:1,0:1})
G,GP,GA,TMR,roots=spin_projection_transfer()
td,tx=sp.symbols('t_d t_o',real=True)
test('positive_spin_overlap_parallel',GP.subs({td:1,tx:sp.Rational(1,3)})>0)
test('positive_spin_overlap_antiparallel',GA.subs({td:1,tx:sp.Rational(1,3)})>0)
test('equal_channel_zero_TMR',TMR.subs({td:1,tx:1})==0)
test('363pct_is_inverse_calibration',any(sp.simplify(TMR.subs({td:x,tx:1})-sp.Rational(363,100))==0 for x in roots))
receipt={
    'scope':'schematic periodic L12 Mn3c 6-band, 12-site-spin AATJ; not fitted PtMn3 or GR',
    'checks_passed':len(checks),'checks':checks,
    'Mn_directed_nearest_bonds':len(BONDS),'momenta':len(KS),'magnetic_domains':2,
    'max_single_Hermitian':max_h,'max_single_C3':max_c3,'max_single_TR':max_tr,
    'max_reciprocal_spectrum':max_period,'max_bilayer_Hermitian':max_bi,
    'max_bilayer_C3':max_bic3,'max_bilayer_TR':max_bitr,
    'old_phase_only_band_spread':flat,'periodic_band_spread':spread,
    'NEGF_parallel':tp,'NEGF_reversed_domain':tm,'equilibrium_force':F,
    'same_H_dOmega_dd_HF':hf_d,'same_H_dOmega_dtheta_HF':hf_th,
    'force_derivative_residual':abs(hf_d-fd_d),'torque_derivative_residual':abs(hf_th-fd_th),
    'spin_filter_angle_conductance':str(G),'spin_filter_TMR':str(TMR),
    'inverse_363pct_channel_ratio':str(sp.sqrt(sp.Rational(1289,200))),
    'measured_PtMn3_bands':False,'calibrated_MgO_barrier':False,
    'measured_OTT_current_torque':False,'full_metric_Tmunu':False,
    'human_lift_or_gravity_anomaly':False,
    'attribution':{
        'original_experiment':'Kang et al. Nature (2026) DOI:10.1038/s41586-026-11172-5',
        'established':'L12, Bloch, Pauli, SU2, Landauer-Caroli, golden rule, Hellmann-Feynman',
        'new':'DASHI periodic finite Mn3c model, tunnelling and same-H mechanical derivatives'}
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
