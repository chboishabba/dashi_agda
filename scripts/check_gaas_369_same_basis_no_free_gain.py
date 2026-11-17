#!/usr/bin/env python3
"""369 SALC basis no-free-gain unitary covariance check.

Proves only that a passively changed basis of exactly the SAME physical
Hamiltonian, dipole, source density and current readout cannot change spectra,
polarized transition probabilities or electric output. A physical perturbation
is different; no 369-specific device is assumed. Numeric states are synthetic.
"""
import json
import numpy as np

w=np.exp(2j*np.pi/3)
U=np.array([[1,1,1],[1,w*w,w],[1,w,w*w]],complex)/np.sqrt(3)
R=np.array([[0,0,1],[1,0,0],[0,1,0]],complex)
H=np.array([[1.9,.06,.02],[.06,2.07,.08],[.02,.08,2.30]],complex)
D=np.diag([.7,1.2,.4]).astype(complex)
J=np.array([[.17,.04j,0],[-.04j,.33,0],[0,0,.11]],complex)
rho=np.array([[.58,.06,.02],[.06,.25,0],[.02,0,.17]],complex)
check=[]
def test(label,ok):
    assert ok,label
    check.append(label)
def transformed(A):return U.conj().T@A@U

test('source U unitary',np.allclose(U.conj().T@U,np.eye(3)))
test('source Fourier spatial intertwiner',np.allclose(R@U,U@np.diag([1,w,w*w])))
test('rho PSD',np.min(np.linalg.eigvalsh(rho))>=-1e-12)
test('rho trace 1',np.isclose(np.trace(rho),1))
for name,A in [('Hamiltonian',H),('dipole',D),('current',J),('state',rho)]:
    B=transformed(A)
    test(name+' Hermiticity',np.allclose(B,B.conj().T))
    test(name+' eigenvalue invariance',np.allclose(np.linalg.eigvalsh(A),np.linalg.eigvalsh(B)))
    test(name+' trace invariance',np.allclose(np.trace(A),np.trace(B)))
    test(name+' trace-square invariance',np.allclose(np.trace(A@A),np.trace(B@B)))
for testkind,A in [('J',J),('D',D),('H',H)]:
    test('same physical density '+testkind,
        np.allclose(np.trace(rho@A),np.trace(transformed(rho)@transformed(A))))
vals,vec=np.linalg.eigh(H)
vals2,vec2=np.linalg.eigh(transformed(H))
test('transition eigenvalues equal',np.allclose(vals,vals2))
for i in range(3):
    for j in range(3):
        original=abs(np.vdot(vec[:,i],D@vec[:,j]))**2
        transported=abs(np.vdot(U.conj().T@vec[:,i],transformed(D)@(U.conj().T@vec[:,j])))**2
        test(f'transition {i}->{j} equal',np.isclose(original,transported))
Hdistorted=H+.08*np.diag([1,-1,0])
test('actual physical perturbation NOT conjugation',
     not np.allclose(np.linalg.eigvalsh(H),np.linalg.eigvalsh(Hdistorted)))
test('no oscillator strength multiplication by U',
     np.isclose(np.trace(D@D.conj().T),np.trace(transformed(D)@transformed(D).conj().T)))
print(json.dumps({'passed':len(check),'all_passed':True,
    'main_statement':'unitary coordinate change alone cannot improve same-source observables',
    'material_Hamiltonian_from_original_369':'OPEN',
    'physical_perturbation_vs_coordinate_change':'DISTINCT',
    'tests':check},indent=2))
