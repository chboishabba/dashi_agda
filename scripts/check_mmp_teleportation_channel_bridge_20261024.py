#!/usr/bin/env python3
"""Bounded Dirac-to-QI channel plus Bennett teleportation reference fixture.
A finite 12-site Wilson-Dirac model, NOT a 4D physical wormhole or
a theorem that ER=EPR creates traversability. Selected input/output
spinor sites supply an explicit tensor-factor/encoding choice.
"""
import numpy as np
from scipy.linalg import expm
I=np.eye(2,dtype=complex)
X=np.array([[0,1],[1,0]],complex)
Z=np.diag([1,-1]).astype(complex)

def hamiltonian(N,r,links,L,q=12,n=1):
    M=len(N);h=L/M;w=.75
    H=np.zeros((2*M,2*M),complex)
    hop=(-1j*X-w*Z)/(2*h)
    for j in range(M):
        k=(j+1)%M
        mass=np.sqrt(n*(n+abs(q)))/r[j] if n else 0.
        H[2*j:2*j+2,2*j:2*j+2]+=N[j]*(mass*Z+w*Z/h)
        block=hop*(N[j]+N[k])*.5*np.exp(1j*links[j])
        H[2*j:2*j+2,2*k:2*k+2]+=block
        H[2*k:2*k+2,2*j:2*j+2]+=block.conj().T
    return H

def dirac_channel():
    M=12;j=np.arange(M);src=1;dst=5
    N=1+.1*np.cos(2*np.pi*j/M)
    r=3.5+.15*np.sin(2*np.pi*j/M)
    links=np.ones(M)*.43/M
    theta=.14*np.sin(2*np.pi*j/M)+.07*np.cos(4*np.pi*j/M)
    G=np.diag(np.repeat(np.exp(1j*theta),2))
    H=hamiltonian(N,r,links,12)
    lg=np.array([links[k]+theta[k]-theta[(k+1)%M] for k in j])
    Hg=hamiltonian(N,r,lg,12)
    gauge_err=np.linalg.norm(Hg-G@H@G.conj().T)
    assert gauge_err<1e-12
    def block(U):return U[2*dst:2*dst+2,2*src:2*src+2]
    K=block(expm(-1j*H*.91))
    Kg=block(expm(-1j*Hg*.91))
    assert np.linalg.norm(Kg-np.exp(1j*(theta[dst]-theta[src]))*K)<1e-12
    missing=I-K.conj().T@K
    eig,vec=np.linalg.eigh(missing)
    assert np.min(eig)>-1e-12
    sqrt_missing=vec@np.diag(np.sqrt(np.maximum(eig,0)))@vec.conj().T
    kraus=[np.vstack((K,np.zeros((1,2),complex)))]
    for i in range(2):
        v=np.zeros((3,2),complex);v[2,:]=sqrt_missing[i,:]
        kraus.append(v)
    trace_resid=np.linalg.norm(sum((A.conj().T@A for A in kraus),np.zeros((2,2),complex))-I)
    assert trace_resid<1e-12
    choi=sum(np.outer(A.flatten(order='F'),A.flatten(order='F').conj()) for A in kraus)
    assert np.linalg.eigvalsh(choi).min()>-1e-12
    for v in (np.array([1,0]),np.array([0,1]),
              np.array([1,1])/np.sqrt(2),np.array([1,1j])/np.sqrt(2)):
        rho=np.outer(v,v.conj())
        out=sum(A@rho@A.conj().T for A in kraus)
        assert abs(np.trace(out)-1)<1e-12
        assert abs(out[2,2].real-(1-np.linalg.norm(K@v)**2))<1e-12
    vals,basis=np.linalg.eigh(H)
    trial=[]
    for t in np.linspace(0,30,1501):
        U=(basis*np.exp(-1j*vals*t))@basis.conj().T
        sv=np.linalg.svd(block(U),compute_uv=False)
        trial.append((float(sum(sv*sv)/2),float(t),sv))
    eta,tbest,sv=max(trial,key=lambda z:z[0])
    weighted_fe=float((sum(sv))**2/4)
    cond_fe=weighted_fe/eta
    assert .20<eta<.22 and .97<cond_fe<.99
    return dict(gauge_error=gauge_err,kraus_TP_error=trace_resid,
                choi_min_eigenvalue=float(np.linalg.eigvalsh(choi).min()),
                best_model_time=tbest,mean_success_probability=eta,
                weighted_entanglement_fidelity=weighted_fe,
                conditional_fidelity_after_herald_and_polar_correction=cond_fe,
                scope='Finite Wilson-Dirac transport, selected spin encoding; NOT MMP global S-matrix')

def bell_teleportation():
    zero=np.array([1,0],complex);one=np.array([0,1],complex)
    phip=(np.kron(zero,zero)+np.kron(one,one))/np.sqrt(2)
    phim=(np.kron(zero,zero)-np.kron(one,one))/np.sqrt(2)
    psip=(np.kron(zero,one)+np.kron(one,zero))/np.sqrt(2)
    psim=(np.kron(zero,one)-np.kron(one,zero))/np.sqrt(2)
    pre_errors=[];post_errors=[]
    for v in (zero,one,(zero+one)/np.sqrt(2),(zero+1j*one)/np.sqrt(2)):
        full=np.kron(v,phip).reshape(2,2,2)
        pre=np.zeros((2,2),complex);post=np.zeros((2,2),complex)
        for b,C in zip((phip,phim,psip,psim),(I,Z,X,Z@X)):
            amp=np.einsum('ab,abc->c',b.conj().reshape(2,2),full)
            rho=np.outer(amp,amp.conj())
            assert abs(np.trace(rho)-.25)<1e-12
            pre+=rho;post+=C@rho@C.conj().T
        pre_errors.append(np.linalg.norm(pre-I/2))
        post_errors.append(np.linalg.norm(post-np.outer(v,v.conj())))
    assert max(pre_errors)<1e-12 and max(post_errors)<1e-12
    return dict(pre_classical_message_marginal_error=max(pre_errors),
                corrected_output_error=max(post_errors),
                required_causal_classical_bits=2,
                scope='Original Bennett-type LOCC teleportation protocol, NOT wormhole transport')

if __name__=='__main__':
    import json
    print(json.dumps({'finite_direct_dirac_channel':dirac_channel(),
                      'LOCC_teleportation_reference':bell_teleportation()},indent=2))
    print('PASS: gauge covariance, CPTP/Choi/erasure, conditional fidelity, Bell LOCC no-signalling')
