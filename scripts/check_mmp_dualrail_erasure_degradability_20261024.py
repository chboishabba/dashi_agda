#!/usr/bin/env python3
"""Construct CPTP receiver/environment degrading maps for equal-loss charged dual rail.

For two equally transmitting charged fermion modes the single-particle
encoded channel is the standard 3-output erasure channel with survival T.
Its complementary channel is the erasure channel with survival 1-T.
Source capacity/degradability: Bennett-DiVincenzo-Smolin 1997, Barnum-
Smolin-Terhal 1998, NOT newly proved by this numerical program.
NOT automatically the general fermionic Gaussian-channel result of
Negari-Salek PRL 137 (2026) 080201.
"""
import numpy as np

def channel(T,rho):
    V=np.zeros((3,3,2),complex)
    for j in (1,2):
        V[j,0,j-1]=np.sqrt(T)
        V[0,j,j-1]=np.sqrt(1-T)
    KB=[V[:,e,:] for e in range(3)]
    KE=[V[b,:,:] for b in range(3)]
    return (sum(K@rho@K.conj().T for K in KB),
            sum(K@rho@K.conj().T for K in KE))

def erase_again(X,p):
    assert 0<=p<=1
    A=np.diag([1,np.sqrt(p),np.sqrt(p)])
    ops=[A]
    for j in (1,2):
        K=np.zeros((3,3),complex)
        K[0,j]=np.sqrt(1-p)
        ops.append(K)
    assert np.linalg.norm(sum(K.conj().T@K for K in ops)-np.eye(3))<1e-12
    return sum(K@X@K.conj().T for K in ops)

def main():
    states=[np.eye(2)/2,np.diag([1,0]),np.diag([0,1]),
        np.ones((2,2))/2,np.array([[.5,-.5j],[.5j,.5]])]
    for T in (.05,.2,.5,.8,.95):
        error=0.
        for rho in states:
            B,E=channel(T,rho)
            if T<=.5:
                target=B
                derived=erase_again(E,T/(1-T))
            else:
                target=E
                derived=erase_again(B,(1-T)/T)
            error=max(error,np.linalg.norm(target-derived))
        assert error<1e-12
        print('T',T,'anti-degradable' if T<=.5 else 'degradable',error)
    print('PASS: source-selected fixed-charge two-mode erasure CPTP degradation / antidegradation')
    print('OPEN: many-body Gaussian mode mixing, physical 4D wormhole channel, global charged Hadamard state')
if __name__=='__main__':
    main()
