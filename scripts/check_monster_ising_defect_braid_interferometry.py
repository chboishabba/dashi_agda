#!/usr/bin/env python3
"""Exact B3 Ising-anyon (braided Ising modular category) observer cut.

Lin--Shao (2021) construct Ising fusion category of Monster CFT duality
defects and discuss a 2+1D Ising x Ising TQFT bulk coupling.
The chiral 1+1D fusion category ALONE does not supply a braiding.
This script selects the standard braided Ising anyon extension; its
2-dimensional three-sigma fusion-space Artin representation is:
sigma1 ~ diag(1,i), sigma2 ~ H sigma1 H, H=Hadamard.
Global phase common to BOTH generators cancels in this exponent-sum-zero
braid word. Exact matrix algebra, not a realized Monster braid operator.
"""
import sympy as s

imag=s.I
H=s.Matrix([[1,1],[1,-1]])/s.sqrt(2)
sigma1=s.diag(1,imag)
sigma2=s.simplify(H*sigma1*H)
identity=s.eye(2)
assert s.simplify(H*H)==identity
assert s.simplify(sigma1*sigma2*sigma1-sigma2*sigma1*sigma2)==s.zeros(2)
central=s.simplify((sigma1*sigma2)**3)
assert central==imag*identity,central
w=s.simplify((sigma1.inv()*sigma2)**3)
assert w==-identity,w
assert s.simplify(w*w.conjugate().T)==identity
assert w.det()==1
# In an isolated fusion space -I is an unobservable global phase.
ket=s.Matrix([1,imag])/s.sqrt(2)
assert s.simplify(ket.conjugate().T*w*ket)[0]==-1
assert all(s.simplify(abs((w*ket)[j])**2-abs(ket[j])**2)==0 for j in range(2))
# A genuinely coherent reference interferometer would instead compare
# amplitudes I and W, producing constructive/destructive differences.
assert s.simplify((identity+w)*ket)==s.zeros(2)
assert s.simplify((identity-w)*ket)==2*ket
print('PASS standard Ising anyon B3 matrices satisfy Artin relation')
print('PASS chosen braid (sigma1^-1 sigma2)^3 = -I exactly')
print('PASS isolated fusion probabilities unchanged; only coherent relative phase is available')
print('SCOPE: not yet a proven braided Monster-defect action or AdS3 gravity observable')
