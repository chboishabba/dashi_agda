#!/usr/bin/env python3
"""Charge-conserving one-fermion dual-rail erasure and coherent-information audit.

Original information-theory authorities: Bennett, DiVincenzo & Smolin,
Phys Rev Lett 78 (1997) 3217; Barnum, Smolin & Terhal, PRA 58 (1998) 3496.
Negari & Salek PRL 137 (2026) 080201 study fermionic Gaussian channels.
Our OUTPUT SPACE HAS EXPLICIT CHARGE-0 ERASURE FLAG: do not equate this
restricted channel with the full Gaussian-channel SDP or an actual MMP
4D Hadamard/Einstein-Maxwell-Dirac fermionic quantum channel.
"""
import json
import math
import numpy as np

def entropy_bits(matrix):
    eig=np.linalg.eigvalsh(matrix)
    assert eig.min()>-1e-12
    return float(-sum(x*math.log2(x) for x in np.clip(eig,0,1) if x>0))

def fixture(T1,T2):
    assert 0<=T1<=1 and 0<=T2<=1
    # Receiver/environment bases are [vacuum, occupied mode 1, mode 2].
    # These two isometric vectors have total fermionic charge +1.
    V=np.zeros((9,2),complex)
    for j,T in enumerate((T1,T2),start=1):
        V[3*j,j-1]=math.sqrt(T)
        V[j,j-1]=math.sqrt(1-T)
    eye=np.eye(2)
    assert np.linalg.norm(V.conj().T@V-eye)<1e-12
    v=V.reshape(3,3,2)
    Kb=[v[:,e,:] for e in range(3)]
    Ke=[v[b,:,:] for b in range(3)]
    assert np.linalg.norm(sum(k.conj().T@k for k in Kb)-eye)<1e-12
    assert np.linalg.norm(sum(k.conj().T@k for k in Ke)-eye)<1e-12
    mixed=eye/2
    B=sum(k@mixed@k.conj().T for k in Kb)
    E=sum(k@mixed@k.conj().T for k in Ke)
    assert np.linalg.norm(B-np.diag([1-(T1+T2)/2,T1/2,T2/2]))<1e-12
    assert np.linalg.norm(E-np.diag([(T1+T2)/2,(1-T1)/2,(1-T2)/2]))<1e-12
    choi=sum(np.outer(k.flatten('F'),k.flatten('F').conj()) for k in Kb)
    assert np.linalg.eigvalsh(choi).min()>-1e-12
    plus=np.ones((2,2))/2
    Bplus=sum(k@plus@k.conj().T for k in Kb)
    Eplus=sum(k@plus@k.conj().T for k in Ke)
    assert abs(Bplus[1,2]-math.sqrt(T1*T2)/2)<1e-12
    assert abs(Eplus[1,2]-math.sqrt((1-T1)*(1-T2))/2)<1e-12
    mean=(T1+T2)/2
    return {'T1':T1,'T2':T2,'mean_success':mean,
      'output_entropy_bits':entropy_bits(B),
      'environment_entropy_bits':entropy_bits(E),
      'coherent_information_bits_maxmixed':entropy_bits(B)-entropy_bits(E),
      'heralded_conditional_entanglement_fidelity':
           (math.sqrt(T1)+math.sqrt(T2))**2/(4*mean) if mean else 0.,
      'receiver_vacuum_probability':float(B[0,0].real),
      'Stinespring_isometry_error':float(np.linalg.norm(V.conj().T@V-eye)),
      'Choi_min_eigenvalue':float(np.linalg.eigvalsh(choi).min())}

def main():
    values={'effective_q12_E020_R240':(.99986528,3.4463e-5),
      'effective_q12_E055_R240':(.9999999936,.9999999968),
      'different_losses':(.2,.7),'balanced_20percent':(.2,.2),
      'balanced_50percent':(.5,.5),'balanced_80percent':(.8,.8),
      'two_distinct_LLL_modes_in_ideal_reduced_static_theory':(1.,1.)}
    data={k:fixture(*v) for k,v in values.items()}
    for T in (0.,.2,.5,.8,1.):
        I=fixture(T,T)['coherent_information_bits_maxmixed']
        assert abs(I-(2*T-1))<1e-12
    assert data['two_distinct_LLL_modes_in_ideal_reduced_static_theory']['coherent_information_bits_maxmixed']==1
    assert data['effective_q12_E020_R240']['coherent_information_bits_maxmixed']<.01
    assert data['effective_q12_E055_R240']['coherent_information_bits_maxmixed']>.999999
    print(json.dumps(data,indent=2))
    print('PASS: charge-conserving dual-rail Stinespring, B/E entropy, Choi, equal-loss erasure coherent-information identity')
    print('OPEN: physically selected S² LLL rail states, 4D globally renormalized Dirac/Einstein solution and actual capacities')
if __name__=='__main__':
    main()
