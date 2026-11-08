#!/usr/bin/env python3
"""Finite two-site Hubbard auxiliary-field projector control.

Reference: Provazza, Knitter et al., arXiv:2611.08129 (2026).
This is a synthetic one-step HS/AFQMC kernel test, not their nickel calculation.
"""
import json
from itertools import product
import numpy as np

rng=np.random.default_rng(261108129)
U=4.0
dt=0.03
t=1.0
k=np.array([[0.,-t],[-t,0.]])
e,v=np.linalg.eigh(k)
half=(v*np.exp(-dt*e/2))@v.T
gamma=np.arccosh(np.exp(dt*U/2))
basis=list(product(range(2),repeat=2))
K=np.kron(k,np.eye(2))+np.kron(np.eye(2),k)
V=np.diag([U*(a==b) for a,b in basis])
H=K+V

# Discrete Hirsch Hubbard-Stratonovich identity for both sites:
# exp[-dt U(n_up-1/2)(n_down-1/2)]
# = 1/2 exp[-dt U/4] sum_{s=+/-1} exp[gamma*s*(n_up-n_down)].
# In the fixed two-electron sector with two sites, combining the
# chemical-potential and HS constants gives exp(-dt*U).
terms=[]
for fields in product((-1,1),repeat=2):
    aa=np.diag([np.exp(gamma*s) for s in fields])
    bb=np.diag([np.exp(-gamma*s) for s in fields])
    A=half@aa@half
    B=half@bb@half
    terms.append(np.kron(A,B))
T_hs=np.exp(-dt*U)*sum(terms)/4

ek,vk=np.linalg.eigh(K)
Khalf=(vk*np.exp(-dt*ek/2))@vk.T
T_ref=Khalf@np.diag(np.exp(-dt*np.diag(V)))@Khalf
error=np.linalg.norm(T_hs-T_ref)
assert error<1e-12, error

# Each field term maps an alpha/beta Slater product to another such product.
a=np.array([.8,.6])
b=np.array([.6,.8])
initial=np.kron(a,b)
expected=T_ref@initial
n=200000
estimate=np.zeros(4)
for _ in range(n):
    estimate+=np.exp(-dt*U)*terms[int(rng.integers(4))]@initial
estimate/=n
mc_error=np.linalg.norm(estimate-expected)
assert mc_error < 0.02

eh,vh=np.linalg.eigh(H)
T_exact=(vh*np.exp(-dt*eh))@vh.T
print(json.dumps({
    "scope":"finite Hubbard one-step HS projector; not phaseless production AFQMC",
    "auxiliary_fields":4,
    "dt":dt,
    "U":U,
    "hs_vs_symmetric_trotter_fro_error":float(error),
    "monte_carlo_samples":n,
    "monte_carlo_one_step_l2_error":float(mc_error),
    "symmetric_trotter_vs_exact_fro_error":float(np.linalg.norm(T_ref-T_exact))
},indent=2))
