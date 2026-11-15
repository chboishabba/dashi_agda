#!/usr/bin/env python3
"""BIDI exact original Griess M81 coherent SL3-vs-C13 Hom-space check.

ORIGINAL priority: Chih-Han Sah (1974), R. L. Griess Jr. (1976
published splitting; 1990 particular Moufang/Albert source).
Character orthogonality is classical; this is subsequent exact
computation, NOT Lean/Agda kernel or physics/Monster source evidence.

Reuses the PREEXISTING full coherent M81 section solver in this PR,
so the two characters are evaluated on ACTUAL same-source group
elements rather than unrelated 26-dimensional proxies.
"""
from collections import Counter
from pathlib import Path
from runpy import run_path
import json,hashlib

root=Path(__file__).resolve().parent
candidate_paths=(root/'check_griess_M81_coherent_SL3_section_steelman_bidi.py',
                 root/'check_griess_coherent_sl3_section_steelman_bidi.py')
donor=next((p for p in candidate_paths if p.is_file()),None)
if donor is None:raise SystemExit('Missing original M81 coherent SL3 section solver')
d=run_path(str(donor))
assert d['G'].order()==5616 and len(d['V'])==27

joint=Counter()
for perm in d['G'].generate_schreier_sims():
 fixed_phase=Counter();fixed=0
 for x in d['V']:
  y,a=d['M81'][perm(d['mindex'][(x,0)])]
  if y==x:
   fixed+=1;fixed_phase[a]+=1
 assert fixed_phase[1]==fixed_phase[2]
 chiJ0=fixed_phase[0]-fixed_phase[2]-1
 chiP26=fixed-1
 joint[chiJ0,chiP26]+=1

expected={(-1,2):1560,(-1,8):104,(0,0):3132,(2,2):819,(26,26):1}
assert joint==expected,(joint,expected)
n=5616
jj=sum(a*a*c for (a,b),c in joint.items())
pp=sum(b*b*c for (a,b),c in joint.items())
jp=sum(a*b*c for (a,b),c in joint.items())
assert (jj,pp,jp)==(n,3*n,0)

# SymPy's Permutation multiplication is LEFT-TO-RIGHT in the sense
# needed here: p01*p12*p20 implements e20(e12(e01(.))).
S=d['S'];lifts=d['lifts'];inds={s:i for i,s in enumerate(S)}
word=lifts[inds[0,1]]*lifts[inds[1,2]]*lifts[inds[2,0]]
assert word.order()==13
for k in range(1,13):
 perm=word**k
 fixed=0;phase=Counter()
 for x in d['V']:
  y,a=d['M81'][perm(d['mindex'][(x,0)])]
  if y==x:
   fixed+=1;phase[a]+=1
 assert phase[1]==phase[2]
 assert (phase[0]-phase[2]-1,fixed-1)==(0,0)

assert 26*26==13*52
print('PASS 5616 actual coherent Griess-M81 elements, JOINT chars:',dict(sorted(joint.items())))
print('PASS full SL3 character mixed numerator = 0, Hom dimension = 0 BOTH directions')
print('PASS coherent order13 word, full C13 mixed character gives Hom dimension 52')
print('BOUNDARY: this is not a Lean/Agda kernel Hom theorem, Jordan/graph/Monster operator')
receipt={
 'original_roots':['Sah 1974','Griess 1976','Griess 1990'],
 'reused_source_solver':donor.name,
 'full_SL3_order':n,
 'joint_histogram':{str(pair):count for pair,count in sorted(joint.items())},
 'character_numerators':{'J0_square':jj,'grade_square':pp,'mixed':jp},
 'complex_Hom_SL3_dim':0,'complex_Hom_C13_dim':52,
 'proof_status':'Exact finite computation; formal Lean/Agda kernel open',
 'script_sha256':hashlib.sha256(Path(__file__).read_bytes()).hexdigest()
}
(root/'griess_coherent_SL3_C13_zeroHom_joint_character_receipt.json').write_text(json.dumps(receipt,indent=2))
