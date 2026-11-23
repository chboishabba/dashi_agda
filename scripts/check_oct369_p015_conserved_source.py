#!/usr/bin/env python3
"""OCT369 P0.15: finite cubic-sector Hamiltonian and closed-interface energy ledger.
Original scientific authority: standard Oh characters, conservation laws,
Newtonian limit of GR. Kang et al. Nature (2026) own PtMn3 OTT/TMR discovery.
DASHI owns this finite composition only. Not measured PtMn3 or antigravity.
"""
import json
from itertools import permutations,product
import sympy as s
q=s.Rational; I=s.eye(3)
sites=[s.Matrix(v) for v in ((0,q(1,2),q(1,2)),(q(1,2),0,q(1,2)),(q(1,2),q(1,2),0))]
rot=[]
for p in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  R=s.zeros(3)
  for i in range(3):R[i,p[i]]=signs[i]
  if R.det()==1:rot.append(R)
def perm(R):
 P=s.zeros(3)
 for a,v in enumerate(sites):
  b=next(i for i,w in enumerate(sites) if tuple(t%1 for t in R*v)==tuple(t%1 for t in w))
  P[b,a]=1
 return P
D=[s.kronecker_product(perm(R),R) for R in rot]
Pt1=q(3,24)*sum((s.trace(R)*d for R,d in zip(rot,D)),s.zeros(9))
Pd=s.kronecker_product(s.ones(3)/3,I)
Pa=Pt1-Pd; Pt2=s.eye(9)-Pt1
x=s.Matrix(s.symbols('x0:9',real=True))
kd,ka,k2=s.symbols('k_d k_a k_2',real=True)
H=kd*Pd+ka*Pa+k2*Pt2
E=s.expand((x.T*H*x)[0]/2)
checks={}
def check(name,test):
 assert test,name
 checks[name]=True
check('orthogonal_idempotent',all(p*p==p for p in (Pd,Pa,Pt2)))
check('ranks_3_3_3',tuple(p.rank() for p in (Pd,Pa,Pt2))==(3,3,3))
check('identity_resolution',Pd+Pa+Pt2==s.eye(9))
check('cubic_Hamiltonian_covariance',all(d*H==H*d for d in D))
check('energy_sector_resolves',s.simplify(E-(kd*(x.T*Pd*x)[0]+ka*(x.T*Pa*x)[0]+k2*(x.T*Pt2*x)[0])/2)==0)
check('energy_even_under_spin_reversal',s.simplify(E-E.subs(dict(zip(x,-x))))==0)
z,Z,alpha,gamma,c,G,r,u=s.symbols('z Z alpha gamma c G r u',real=True)
V=alpha*u*(z-Z)
Fbody=-s.diff(V,z); Fsupport=-s.diff(V,Z)
check('interface_action_reaction',Fbody+Fsupport==0)
check('gradient_control',s.simplify(Fbody+alpha*u)==0)
W=s.symbols('W_drive',real=True)
Ectrl=s.symbols('E_controller',real=True)
Emat=E+W; Econtroller=Ectrl-W
Etotal=s.simplify(Emat+Econtroller+V)
check('closed_drive_energy_cancelled',s.diff(Etotal,W)==0)
check('material_receives_work',s.diff(Emat,W)==1)
check('controller_pays_work',s.diff(Econtroller,W)==-1)
Phi=-G*Etotal/(c*c*r)
check('closed_system_gravity_no_internal_work_artifact',s.diff(Phi,W)==0)
check('subsystem_vs_total_gravity_distinct',s.diff(-G*Emat/(c*c*r),W)==-G/(c*c*r))
check('no_force_without_external_coupling',Fbody.subs(alpha,0)==0)
check('body_force_has_equal_reaction',Fbody+Fsupport==0 and Fbody!=0)
check('reversal_sign_force',Fbody.subs(u,-u)+Fbody==0)
check('gravity_weak_field_source_dE',s.diff(Phi,Ectrl)==-G/(c*c*r))
check('minimum_lift_force',q(70)*q(980665,100000)==q(1372931,2000))
receipt={'checks_passed':len(checks),'checks':list(checks),
 'sector_ranks':{'T1g_uniform_dipole':3,'T1g_AFM':3,'T2g_AFM':3},
 'body_force':str(Fbody),'support_reaction':str(Fsupport),
 'closed_drive_energy_derivative':str(s.diff(Etotal,W)),
 'gravity_internal_work_derivative':str(s.diff(Phi,W)),
 'actual_PtMn3_Hamiltonian_fitted':False,'complete_Tmunu_derived':False,
 'anomalous_gravity_measured':False,'human_lift_measured':False,
 'attribution':{'original_experiment':'Jaimin Kang et al., Nature 2026 doi:10.1038/s41586-026-11172-5',
 'original_physics':'standard cubic-group representation, energy-momentum conservation and weak-field GR',
 'repo_priors':'DASHI P0.14, Atomic369, CMP119 firewall, NingLiYBCO static constraint, Amy attribution firewall',
 'new_DASHI':'finite same-carrier energy/force ledger; no original antigravity claim'}}
if __name__=='__main__':print(json.dumps(receipt,indent=2))
