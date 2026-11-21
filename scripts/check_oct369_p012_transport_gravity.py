#!/usr/bin/env python3
"""P0.12 exact C3 three-sublattice transport-to-gravity preflight.
Uses paper-reported beta_eff=beta_intra-beta_inter structural relation.
NOT a physical PtMn3 Hamiltonian, tensor, or gravitational measurement.
"""
import json
import sympy as sp
b1,b2,theta,J,h,G,c,r=sp.symbols('beta_intra beta_inter theta J h G c r', real=True)
I=sp.eye(3); O=sp.ones(3); K=sp.Matrix([[0,0,1],[1,0,0],[0,1,0]])
L=(b1-b2)*I+b2*O
u=sp.ones(3,1); v=sp.Matrix([1,-1,0])
assert K**3==I
assert L*u==(b1+2*b2)*u
assert L*v==(b1-b2)*v
assert K*L==L*K
assert L.subs(b1,b2)*v==sp.zeros(3,1)
pi=sp.pi
P=[sp.Matrix([sp.cos(2*pi*k/3),sp.sin(2*pi*k/3)]) for k in range(3)]
R=sp.Matrix([[sp.cos(theta),-sp.sin(theta)],[sp.sin(theta),sp.cos(theta)]])
S=[R*p for p in P]
assert all(sp.simplify(x)==0 for x in sum(P,sp.zeros(2,1)))
assert all(sp.simplify(x)==0 for x in sum(S,sp.zeros(2,1)))
Q=[sp.simplify(sum((L[a,b]*P[b] for b in range(3)),sp.zeros(2,1))) for a in range(3)]
assert all(sp.simplify(Q[a]-(b1-b2)*P[a])==sp.zeros(2,1) for a in range(3))
cross=lambda x,y:sp.det(sp.Matrix.hstack(x,y))
tau=sp.trigsimp(sum(cross(S[a],Q[a]) for a in range(3)))
assert sp.trigsimp(tau+3*(b1-b2)*sp.sin(theta))==0
assert sp.simplify(tau.subs(b1,b2))==0
Eex=sp.trigsimp(J*sum((S[a].dot(S[b]) for a in range(3) for b in range(a+1,3))))
assert sp.trigsimp(Eex+sp.Rational(3,2)*J)==0
assert sp.simplify(sp.diff(Eex,theta))==0
E=Eex-h*sp.cos(theta)
Eflip=sp.trigsimp(E.subs(theta,theta+sp.pi)-E)
assert sp.trigsimp(Eflip-2*h*sp.cos(theta))==0
phi=-G*E/(c**2*r)
grad=sp.diff(phi,r)
deltaPhi=sp.trigsimp(phi.subs(theta,theta+sp.pi)-phi)
assert sp.trigsimp(deltaPhi+2*G*h*sp.cos(theta)/(c**2*r))==0
assert sp.diff(phi,b1)==0 and sp.diff(phi,b2)==0
P0=O/3; Ps=I-P0
assert P0*P0==P0 and Ps*Ps==Ps and P0*Ps==sp.zeros(3)
assert sp.simplify(L-(b1+2*b2)*P0-(b1-b2)*Ps)==sp.zeros(3)
receipt={
 'scope':'schematic three-site C3 torque-sector operator; NOT material PtMn3 or GR fit',
 'source_theory_beta_eff':'beta_intra-beta_inter',
 'uniform_channel_eigenvalue':str(b1+2*b2),
 'staggered_channel_eigenvalue':str(b1-b2),
 'generalized_octupole_angle_torque':str(tau),
 'exchange_energy':str(Eex),
 'order_reversal_energy_delta':str(Eflip),
 'conventional_subsystem_gravity_potential':str(phi),
 'order_reversal_gravity_potential_delta':str(deltaPhi),
 'symmetry_controls':{'C3_order3':True,'total_spin_zero':True,'beta_equal_zero_staggered_torque':True,'nonconservative_transport_not_assumed_energy_source':True},
 'actual_octupole_tensor_derived':False,
 'actual_PtMn3_H_k_derived':False,
 'full_apparatus_Tmunu_derived':False,
 'nonminimal_gravity_inferred':False,
 'assert_statements_passed':17,
}
if __name__=='__main__':print(json.dumps(receipt,sort_keys=True,indent=2))
