#!/usr/bin/env python3
"""Exact C3 Fourier inversion and zero/phase separation for the Monster 3B 12+78 cut.

Reuse (not replacements):
  TriadicDepthOneCharacters: phase0 = 1, phase1 = zeta, phase2 = zeta^2;
  PhaseEnrichedTrit and ZeroValueFibreNontrivialityExact: observed neutral 0;
  MonsterC3CyclotomicEvaluationExact: complete regular-character cancellation;
  Monster3BBalancedRegularFibreExact: 65610 regular blocks + residual 53;
  Monster3BZetaSuzukiDiagonalNormCutsetExact: four S90 fingerprints.
Original finite Fourier: Terras (1999); character theory: Serre (1977);
Monster 3B restriction: Barraclough and Wilson (2007).

No complex rounding, Monster matrix, or new root-of-unity algebra.
"""
from fractions import Fraction as F
from itertools import product
import argparse,json
from pathlib import Path
ZERO=(F(0),F(0))
ROOT=((F(1),F(0)),(F(0),F(1)),(F(-1),F(-1)))
def add(*xs):return tuple(sum(x[i] for x in xs) for i in range(2))
def mul(x,y):
 a,b=x;c,d=y
 return (a*c-b*d,a*d+b*c-b*d)
def scale(n,x):return n*x[0],n*x[1]
def zeta(k):return ROOT[k%3]
def norm(x):return x[0]**2-x[0]*x[1]+x[1]**2
def cyclo(x):return [int(x[0]),int(x[1])]
def eval_c3(m,k):
 if len(m)!=3 or any(type(n) is not int or n<0 for n in m):
  raise ValueError("three nonnegative integer phase dimensions required")
 return add(*(scale(F(n),zeta(j*k)) for j,n in enumerate(m)))
def invert_c3(traces):
 if len(traces)!=3:raise ValueError("identity, z, z² character values required")
 m=[]
 for j in range(3):
  n=scale(F(1,3),add(*(mul(zeta(-j*k),traces[k]) for k in range(3))))
  if n[1]!=0 or n[0].denominator!=1 or n[0]<0:
   raise ValueError("not a nonnegative integral C3 character")
  m.append(int(n[0]))
 return tuple(m)
def audit():
 assert zeta(0)==(1,0)!=ZERO
 assert add(*ROOT)==ZERO and mul(zeta(1),zeta(2))==zeta(0)
 proj=[]
 for a in range(3):
  row=[]
  for j in range(3):
   p=scale(F(1,3),add(*(zeta(k*(a-j)) for k in range(3))))
   assert p==(F(int(a==j)),F(0))
   row.append(int(a==j))
  proj.append(row)
 assert proj==[[1,0,0],[0,1,0],[0,0,1]]
 choices={"directSym2_zeta":(0,12,78),"dualSym2_zeta":(0,90,0),
          "directSym2_zetaSquared":(0,78,12),
          "dualSym2_zetaSquared":(0,0,90)}
 rows={}
 for name,m in choices.items():
  traces=tuple(eval_c3(m,k) for k in range(3))
  assert invert_c3(traces)==m and sum(m)==90 and m[0]==0 and traces[1]!=ZERO
  rows[name]={"phase_dimensions_1_zeta_zetaSquared":m,
              "traces_e_z_z2":[cyclo(t) for t in traces],
              "norm_of_nonidentity_trace":int(norm(traces[1])),
              "no_trivial_eigenvectors":True,"zero_operator_eigenvalue":False}
 assert [rows[k]["norm_of_nonidentity_trace"] for k in choices]==[5292,8100,5292,8100]
 W=(65663,65610,65610);regular=(65610,)*3;empty=(0,0,0)
 wtr=[eval_c3(W,k) for k in range(3)]
 rr=[eval_c3(regular,k) for k in range(3)]
 ee=[eval_c3(empty,k) for k in range(3)]
 assert list(map(cyclo,wtr))==[[196883,0],[53,0],[53,0]]
 assert list(map(cyclo,rr))==[[196830,0],[0,0],[0,0]]
 assert rr[1]==ee[1]==ZERO and rr[0]!=ee[0]
 assert invert_c3(wtr)==W and invert_c3(rr)==regular
 checked=0
 for m in product(range(11),repeat=3):
  assert invert_c3([eval_c3(m,k) for k in range(3)])==m
  assert (eval_c3(m,1)==ZERO)==(m[0]==m[1]==m[2])
  checked+=1
 for invalid in (((0,1),(0,0),(0,0)),((1,0),(0,1),(0,1))):
  try:invert_c3(invalid)
  except ValueError:pass
  else:raise AssertionError("non-character triple accepted")
 return {"status":"exact finite C3 Fourier/zero distinction passed",
    "tests_of_nonnegative_multiplicity_triples":checked,
    "phase0_exponent_means_eigenvalue_one":True,
    "phase0_is_scalar_zero":False,
    "C3_projector_on_eigenphase_matrix":proj,
    "Suzuki90_candidate_triples":rows,
    "all_Suzuki90_trivial_eigenspaces_empty":True,
    "all_Suzuki90_nonidentity_character_traces_nonzero":True,
    "MonsterW_eigen_dimensions_1_zeta_zetaSquared":W,
    "MonsterW_character_e_z_z2":list(map(cyclo,wtr)),
    "MonsterW_regular_bulk_eigen_dimensions":regular,
    "MonsterW_regular_bulk_character_e_z_z2":list(map(cyclo,rr)),
    "empty_representation_character_e_z_z2":list(map(cyclo,ee)),
    "nonidentity_trace_zero_does_not_imply_empty":True,
    "actual_Monster_selected_Suzuki_pair_recognized":False,
    "balanced_trit_zero_equated_with_C3_phase0":False}
if __name__=="__main__":
 p=argparse.ArgumentParser();p.add_argument("--receipt",type=Path);a=p.parse_args()
 text=json.dumps(audit(),indent=2)+"\n"
 if a.receipt:a.receipt.write_text(text)
 print(text,end="")
