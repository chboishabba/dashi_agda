#!/usr/bin/env python3
"""Independent fermionic loss: single-angular-mode qubit vs two-mode parity qubit.

Source algebra: merged Lean dashi_lean4 #37 MajoranaParityQubitExact,
#76 QuantumMereologyFiniteSubsetMarginal/PartialTraceCoherence.
Actual source-selected angular modes are NOT automatically isolated Majoranas;
this tests a FREE two-complex-fermion occupancy encoding only.
"""
import json
import numpy as np
I2=np.eye(2,dtype=complex)
I4=np.eye(4,dtype=complex)

def audit(T1,T2):
    assert 0<=T1<=1 and 0<=T2<=1
    t1,t2=np.sqrt([T1,T2]);s1,s2=np.sqrt([1-T1,1-T2])
    D1=np.diag([1,t1]);D2=np.diag([1,t2])
    L1=np.array([[0,s1],[0,0]],complex)
    L2=np.array([[0,s2],[0,0]],complex)
    kraus=[np.kron(a,b) for a in (D1,L1) for b in (D2,L2)]
    tp4=np.linalg.norm(sum((k.conj().T@k for k in kraus),np.zeros((4,4),complex))-I4)
    assert tp4<1e-12
    # Fock basis 00,01,10,11: embedded logical basis 00/11.
    V=np.array([[1,0],[0,0],[0,0],[0,1]],complex)
    P=V@V.conj().T
    even=[V.conj().T@P@k@V for k in kraus]
    assert np.linalg.norm(even[1])+np.linalg.norm(even[2])<1e-12
    assert abs(even[3][0,1]-s1*s2)<1e-12
    # Output is an even logical qubit OR a flagged odd-parity erasure.
    out=[np.vstack((k,np.zeros((1,2),complex))) for k in even]
    for k in kraus:
        leaked=(I4-P)@k@V
        for j in (1,2):
            a=np.zeros((3,2),complex);a[2,:]=leaked[j,:];out.append(a)
    tp3=np.linalg.norm(sum((k.conj().T@k for k in out),np.zeros((2,2),complex))-I2)
    assert tp3<1e-12
    choi=sum(np.outer(k.ravel(order='F'),k.ravel(order='F').conj()) for k in out)
    assert np.linalg.eigvalsh(choi).min()>-1e-12
    one_particle=(T1+T2)/2
    no_loss=(1+T1*T2)/2
    even_parity=(1+T1*T2+(1-T1)*(1-T2))/2
    double_loss=(1-T1)*(1-T2)/2
    assert abs(even_parity-no_loss-double_loss)<1e-12
    measured_even=sum(np.trace(k@I2/2@k.conj().T).real for k in even)
    assert abs(measured_even-even_parity)<1e-12
    fe=(1+np.sqrt(T1*T2))**2/4
    assert fe<=no_loss+1e-12
    return dict(T1=T1,T2=T2,
        one_particle_mode_mean_success=one_particle,
        parity_qubit_no_loss_herald_success=no_loss,
        parity_qubit_even_only_acceptance=even_parity,
        double_loss_false_acceptance=double_loss,
        parity_only_accepted_entanglement_fidelity=fe/even_parity,
        actual_no_loss_conditional_entanglement_fidelity=fe/no_loss,
        fock_TP_residual=float(tp4),encoded_TP_residual=float(tp3),
        choi_min_eigenvalue=float(np.linalg.eigvalsh(choi).min()))
def main():
    vals={'q12_E0.20_R240':(.99986528,3.4463e-5),
          'q12_E0.55_R240':(.9999999936,.9999999968),
          'adversarial_attenuation':(.2,.7),
          'full_loss':(0.,0.),'lossless':(1.,1.)}
    out={name:audit(*xs) for name,xs in vals.items()}
    assert abs(out['adversarial_attenuation']['double_loss_false_acceptance']-.12)<1e-12
    assert out['full_loss']['parity_qubit_even_only_acceptance']==1.
    assert out['full_loss']['parity_qubit_no_loss_herald_success']==.5
    assert out['full_loss']['one_particle_mode_mean_success']==0.
    print(json.dumps(out,indent=2))
    print('PASS 4x4 two-fermion Fock Kraus, 3x2 erasure Choi, parity vs no-loss distinction')
    print('OPEN same-object 4D MMP Dirac Fock scattering and physical Majorana encoding')
if __name__=='__main__': main()
