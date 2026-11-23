#!/usr/bin/env python3
"""Bounded search for original ATLAS C,D words in actual Monster E/Z(E) matrices.

Input must be the existing mmgroup producer's manifest. The finite search
tests necessary quotient relations and an exact common GL12(F3) intertwiner.
Success is a *candidate word correspondence* until original Monster group
word identity and whole quotient isomorphism are independently certified.
"""
import argparse
import json
from collections import deque
from pathlib import Path
from monster3b_atlas_mmgroup_cross_source_intertwiner_gate import (
 atlas, eye, neg, mul, inverse, powm, monster_matrix, check_pair
)

def freeze(m):return bytes(x for row in m for x in row)
def enumerate_words(gens,limit,depth):
 alphabet=[(name,m,lam) for name,(m,lam) in gens.items()]
 alphabet.extend((name+"^-1",inverse(m),lam) for name,(m,lam) in gens.items())
 queue=deque([(eye(),1,[])])
 seen={freeze(eye())}
 output=[]
 while queue:
  m,phase,word=queue.popleft()
  if word:output.append((m,phase,word))
  if len(word)>=depth:continue
  for label,g,p in alphabet:
   # Adjacent cancellation is excluded only when known inverse tokens.
   if word and (word[-1]+"^-1"==label or label+"^-1"==word[-1]):continue
   nxt=mul(m,g);key=freeze(nxt)
   if key in seen:continue
   if len(seen)>=limit:raise ValueError("finite exploration budget hit; no negative existence claim")
   seen.add(key);queue.append((nxt,phase*p%3,word+[label]))
 return output
def search(atlas_pair,gens,depth,limit,pair_limit):
 C,D=atlas_pair
 words=enumerate_words(gens,limit,depth)
 Ic=eye();mc=neg(Ic)
 cr=[(m,w) for m,p,w in words if p==2 and powm(m,2)==mc]
 dr=[(m,w) for m,p,w in words if p==1 and powm(m,3)==Ic and m!=Ic]
 tested=0;hits=[]
 for a,wa in cr:
  for b,wb in dr:
   ab=mul(a,b)
   if powm(ab,28)!=mc:continue
   tested+=1
   if tested>pair_limit:raise ValueError("pair examination budget hit; result is partial")
   receipt=check_pair((C,D),(a,b))
   if receipt["invertible_basis_witness"]:
    hits.append(dict(C_word=wa,D_word=wb,
                     generator_relation_CD28_minusI=True,
                     intertwiner_dimension=receipt["intertwiner_dimension"],
                     T_rows_F3=receipt["T_rows_F3"],
                     provenance="CANDIDATE_ONLY_unverified_original_quotient_word_identification"))
 return dict(schema="monster3b-atlas-mmgroup-bounded-quotient-search-v1",
   enumerated_distinct_quotient_matrices=len(words)+1,
   C_square_negative_I_candidate_count=len(cr),
   D_cube_identity_candidate_count=len(dr),
   relation_filtered_pairs_tested=tested,
   candidate_intertwiners=hits,
   search_exhaustive_only_bounded_word_depth=True,
   actual_Monster_element_words_rechecked_in_mmgroup=False,
   original_ATLAS_quotient_isomorphism_proved=False,
   selected_Hom_and_VOA_promoted=False)
def main():
 ap=argparse.ArgumentParser()
 ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
 ap.add_argument("--manifest",type=Path,required=True)
 ap.add_argument("--depth",type=int,default=4)
 ap.add_argument("--max-states",type=int,default=20000)
 ap.add_argument("--max-pairs",type=int,default=100)
 ap.add_argument("--out",type=Path)
 ns=ap.parse_args()
 if ns.depth<1 or ns.depth>8 or ns.max_states<1 or ns.max_pairs<1:ap.error("bounded positive limits required")
 manifest=json.loads(ns.manifest.read_text())
 lifts=manifest.get("normalizer_lifts",[])
 if len(lifts)!=2 or {x.get("name") for x in lifts}!={"g3b","h3b"}:
  raise ValueError("requires exact mmgroup 3B source normalizer manifest")
 gens={}
 for lift in lifts:
  phase=lift.get("central_image")
  if type(phase)!=int or phase not in (-1,1):
   raise ValueError("missing source central phase")
  gens[lift["name"]]=(monster_matrix(lift),phase%3)
 out=search(atlas(ns.root),gens,ns.depth,ns.max_states,ns.max_pairs)
 s=json.dumps(out,indent=2,sort_keys=True)+"\n"
 if ns.out:ns.out.write_text(s)
 print(s,end="")
if __name__=="__main__":main()
