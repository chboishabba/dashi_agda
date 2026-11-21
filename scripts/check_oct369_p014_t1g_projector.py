#!/usr/bin/env python3
"""OCT369 P0.14 L12 Mn(3c) exact cubic T1g / T2g magnetic projector.
Exact representation test; NOT a published PtMn3 domain, transport, stress,
or gravitational anomaly result.
"""
from itertools import permutations,product
import sympy as s
import json
q=s.Rational
I=s.eye(3)
sites=[s.Matrix(v) for v in ((0,q(1,2),q(1,2)),(q(1,2),0,q(1,2)),(q(1,2),q(1,2),0))]
rot=[]
for p in permutations(range(3)):
 for signs in product((-1,1),repeat=3):
  R=s.zeros(3)
  for i in range(3): R[i,p[i]]=signs[i]
  if R.det()==1:rot.append(R)
def residual(v):return tuple(a%1 for a in v)
def site_perm(R):
 P=s.zeros(3)
 for a,x in enumerate(sites):
  b=next(i for i,y in enumerate(sites) if residual(y)==residual(R*x))
  P[b,a]=1
 return P
D=[s.kronecker_product(site_perm(R),R) for R in rot]
PT1=q(3,24)*sum((s.trace(R)*d for R,d in zip(rot,D)),s.zeros(9))
Pdip=s.kronecker_product(s.ones(3)/3,I)
Pafm=PT1-Pdip
PT2=s.eye(9)-PT1
centre=sum(sites,s.zeros(3,1))/3
trial=s.Matrix.vstack(*[v-centre for v in sites])
checks={
 '24_rotations':len(rot)==24,
 'site_rotations_permutation':all(site_perm(R)*site_perm(R).T==I for R in rot),
 'T1_is_projector':PT1**2==PT1,'T1_rank_6':PT1.rank()==6,
 'dipole_is_projector':Pdip**2==Pdip,'dipole_rank_3':Pdip.rank()==3,
 'T1g_AFM_is_projector':Pafm**2==Pafm,'T1g_AFM_rank_3':Pafm.rank()==3,
 'T2g_is_projector':PT2**2==PT2,'T2g_rank_3':PT2.rank()==3,
 'resolution_identity':Pdip+Pafm+PT2==s.eye(9),
 'mutually_orthogonal':Pdip*Pafm==s.zeros(9) and Pdip*PT2==s.zeros(9) and Pafm*PT2==s.zeros(9),
 'AFM_group_equivariant':all(d*Pafm==Pafm*d for d in D),
 'T1_group_equivariant':all(d*PT1==PT1*d for d in D),
 'trial_in_T1g_AFM':Pafm*trial==trial,
 'trial_zero_dipole':Pdip*trial==s.zeros(9,1),
 'trial_zero_T2g':PT2*trial==s.zeros(9,1),
 'trial_nonzero':trial!=s.zeros(9,1),
 'trial_net_spin_zero':sum((trial[3*a:3*a+3,0] for a in range(3)),s.zeros(3,1))==s.zeros(3,1),
 'inversion_site_axial_even':all(residual(-v)==residual(v) for v in sites),
 'time_reversal_odd':Pafm*(-trial)==-trial,
}
for name,passed in checks.items(): assert passed,name
if __name__=='__main__':
 print(json.dumps({'scope':'L12 prototype cubic irrep, not experimental PtMn3 or gravity','checks_passed':len(checks),'checks':checks,
 'sector_ranks':{'T1g_dipole':3,'T1g_AFM':3,'T2g_AFM':3},'trial_in_T1g_AFM':True,
 'material_domain_identification':False,'material_Hk_and_transport':False,
 'total_stress_energy':False,'gravity_effect':False},indent=2,sort_keys=True))
