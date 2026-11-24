#!/usr/bin/env python3
"""Fail-closed ATLAS <-> Monster E/Z(E) exact GF(3) generator-pair screen.

The actual Monster manifest must originate in the existing mmgroup producer
monster_3b_mmgroup_source_symplectic_basis.py. A supplied generator-word map
is a *candidate*, never an authenticated quotient isomorphism merely because
this linear test passes. Original source owners: ATLAS/AtlasRep, the published
MonsterSubgroups group words, existing DASHI PRs #1098/#1250.
"""
import argparse
import hashlib
import json
from pathlib import Path

MOD=3
N=12
SOURCES={
 "2Suzd2G1-f3r12aB0.m1":"ddd4919ab560f78b065aa08e309bd047942cdb7bb52a1474da84d54d35a031c2",
 "2Suzd2G1-f3r12aB0.m2":"433ba0f0373995b159859df00dd5a5005355fdbf8b59a31d651aeaf43ffcd15f",
}
def eye():return [[int(i==j) for j in range(N)] for i in range(N)]
def neg(a):return [[-x%3 for x in row] for row in a]
def mul(a,b):return [[sum(a[i][k]*b[k][j] for k in range(N))%3 for j in range(N)] for i in range(N)]
def transpose(a):return [list(r) for r in zip(*a)]
def scaled(a,s):return [[s*x%3 for x in row] for row in a]
def powm(a,n):
 if n<0:return powm(inverse(a),-n)
 out=eye()
 while n:
  if n&1:out=mul(out,a)
  a=mul(a,a);n//=2
 return out
def rref(rows,ncols):
 rows=[[int(v)%3 for v in row] for row in rows]
 piv=[];r=0
 for c in range(ncols):
  k=next((i for i in range(r,len(rows)) if rows[i][c]),None)
  if k is None:continue
  rows[r],rows[k]=rows[k],rows[r]
  inv=rows[r][c] # inverse of 1 or 2 in F3 equals itself
  rows[r]=[(x*inv)%3 for x in rows[r]]
  for i in range(len(rows)):
   if i!=r and rows[i][c]:
    d=rows[i][c];rows[i]=[(x-d*y)%3 for x,y in zip(rows[i],rows[r])]
  piv.append(c);r+=1
  if r==len(rows):break
 return rows,piv
def rank(a):return len(rref(a,len(a[0]))[1])
def inverse(a):
 rows=[a[i][:]+eye()[i] for i in range(N)]
 x,p=rref(rows,2*N)
 if p[:N]!=list(range(N)):raise ValueError("singular GL12 candidate")
 return [row[N:] for row in x[:N]]
def kernel(pairs):
 equations=[]
 for a,b in pairs:
  for i in range(N):
   for j in range(N):
    row=[0]*(N*N)
    for k in range(N):
     row[i*N+k]=(row[i*N+k]+a[k][j])%3
     row[k*N+j]=(row[k*N+j]-b[i][k])%3
    equations.append(row)
 matrix,piv=rref(equations,N*N)
 pivset=set(piv);basis=[]
 for c in range(N*N):
  if c in pivset:continue
  v=[0]*(N*N);v[c]=1
  for i,p in enumerate(piv):v[p]=(-matrix[i][c])%3
  basis.append([v[i*N:(i+1)*N] for i in range(N)])
 return basis
def atlas(root):
 base=root/"data"/"atlas"
 out=[]
 for filename,sha in SOURCES.items():
  blob=(base/filename).read_bytes()
  if hashlib.sha256(blob).hexdigest()!=sha:raise ValueError("ATLAS source SHA mismatch: "+filename)
  words=blob.decode().split()
  if [int(x) for x in words[:4]]!=[1,3,12,12]:raise ValueError("wrong MeatAxe metadata")
  s="".join(words[4:])
  if len(s)!=144 or set(s)-set("012"):raise ValueError("wrong ATLAS matrix")
  out.append([[int(v) for v in s[i*12:(i+1)*12]] for i in range(12)])
 return out
def standard_j():
 j=[[0]*N for _ in range(N)]
 for i in range(6):j[i][6+i]=1;j[6+i][i]=2
 return j
def monster_matrix(lift):
 coords=lift.get("translation_images",[])+lift.get("modulation_images",[])
 if len(coords)!=N:raise ValueError("Monster source must supply 12 generator images")
 cols=[]
 for item in coords:
  v=item.get("a",[])+item.get("b",[])
  if len(v)!=N or any(type(x)!=int or x not in (0,1,2) for x in v):
   raise ValueError("invalid Monster E/Z(E) coordinates")
  cols.append(v)
 return transpose(cols)
def candidate_word(word, gens):
 if not word or len(word)>200 or not isinstance(word,list):raise ValueError("explicit nonempty bounded generator word required")
 z=eye();phase=1
 for token in word:
  if not isinstance(token,str) or token.rstrip("^-1") not in gens and token not in gens:
   raise ValueError("unknown Monster source generator token")
  invert=token.endswith("^-1");key=token[:-3] if invert else token
  if key not in gens:raise ValueError("unknown Monster generator")
  a,lam=gens[key]
  z=mul(z,inverse(a) if invert else a)
  phase=phase*(lam if not invert else lam)%3
 return z,phase
def form_source():
 from monster3b_atlas_actual_d4_word_witness import FORM_ROWS
 return [[int(c) for c in line] for line in FORM_ROWS.splitlines()]
def form_monster():
 # The existing MonsterSubgroups adapter normalizes [B_i,A_j]=z^delta.
 # Therefore the commutator form has lower-left +I and upper-right -I.
 j=[[0]*N for _ in range(N)]
 for i in range(6):j[i][6+i]=2;j[6+i][i]=1
 return j
def cocycle_defect(g,phase):
 c=[[0]*N for _ in range(N)]
 for i in range(6):c[6+i][i]=1
 transported=mul(mul(transpose(g),c),g)
 defect=[[(transported[i][j]-phase*c[i][j])%3 for j in range(N)] for i in range(N)]
 return defect
def atlas_relator(c,d):
 # Source-original ATLAS 2.Suz:2 semipresentation word, including inverses.
 # The separate source relation has exact order seven, not simply power=identity.
 ci=inverse(c);di=inverse(d)
 letters={"c":ci,"d":di,"C":c,"D":d}
 product=eye()
 for k in "cdcdcddcdd":product=mul(product,letters[k])
 return product

def source_relations(c,d):
 unit=eye(); minus=neg(unit)
 return (powm(c,2)==minus and powm(d,3)==unit and d!=unit
         and powm(mul(c,d),28)==minus
         and powm(mul(c,d),56)==unit
         and powm(atlas_relator(c,d),7)==unit
         and atlas_relator(c,d)!=unit)

def check_pair(atlas_pair,monster_pair,actual_forms=False):
 c,d=atlas_pair;b,cand=monster_pair
 if not source_relations(c,d):
  raise ValueError("original ATLAS source generator semipresentation missing")
 if not source_relations(b,cand):
  return {"status":"REJECTED_TARGET_RELATIONS","intertwiner_dimension":None}
 basis=kernel([(b,c),(cand,d)])
 invertible=[t for t in basis if rank(t)==N] if len(basis)==1 else []
 out={"status":"ALGEBRAIC_CANDIDATE_ONLY" if invertible else "NO_INVERTIBLE_INTERTWINER_CERTIFIED",
      "intertwiner_dimension":len(basis),"invertible_basis_witness":len(invertible)==1,
      "original_generator_word_correspondence_authenticated":False,
      "actual_Monster_Hom_promoted":False}
 if invertible:
  t=invertible[0]
  assert mul(c,t)==mul(t,b) and mul(d,t)==mul(t,cand)
  out["T_rows_F3"]=t
  out["T_rank"]=12
  if actual_forms:
   ja,jm=form_source(),form_monster()
   if (mul(mul(transpose(c),ja),c)!=neg(ja) or
       mul(mul(transpose(d),ja),d)!=ja):
    raise ValueError("original ATLAS source similitude form mismatch")
   for g,phase in ((b,2),(cand,1)):
    if mul(mul(transpose(g),jm),g)!=scaled(jm,phase):
     raise ValueError("Monster quotient symplectic similitude mismatch")
   transported=mul(mul(transpose(t),ja),t)
   factors=[phase for phase in (1,2) if transported==scaled(jm,phase)]
   if len(factors)!=1:
    out["status"]="FORM_TRANSPORT_NOT_CERTIFIED"
    out["form_transport_passed"]=False
   else:
    out["form_transport_passed"]=True
    out["form_scale_mod3"]=factors[0]
    defects=[cocycle_defect(b,2),cocycle_defect(cand,1)]
    if any(z!=transpose(z) for z in defects):
     raise ValueError("Monster Heisenberg cocycle defect not symmetric")
    out["cocycle_defect_ranks"]=[rank(z) for z in defects]
    out["quadratic_central_corrections_derived"]=True
  else:out["actual_cross_source_form_test_run"]=False
 return out
def test(root):
 C,D=atlas(root)
 a=check_pair((C,D),(C,D))
 assert a["intertwiner_dimension"]==1 and a["invertible_basis_witness"]
 assert check_pair((C,D),(D,C))["status"]=="REJECTED_TARGET_RELATIONS"
 assert check_pair((C,D),(eye(),eye()))["status"]=="REJECTED_TARGET_RELATIONS"
 t=a["T_rows_F3"]
 assert t==eye() or mul(C,t)==mul(t,C)
 return {"status":"PASS_GF3_SAME_SOURCE_FIXTURE","same_source_nullity":1,
         "negative_wrong_generator":True,"negative_trivial_target":True,
         "independent_Monster_generator_words_proven":False}
def main():
 ap=argparse.ArgumentParser()
 ap.add_argument("--root",type=Path,default=Path(__file__).resolve().parents[1])
 ap.add_argument("--manifest",type=Path)
 ap.add_argument("--words",type=Path)
 ap.add_argument("--out",type=Path)
 args=ap.parse_args()
 C,D=atlas(args.root)
 if args.manifest is None and args.words is None:result=test(args.root)
 else:
  if args.manifest is None or args.words is None:ap.error("both actual mmgroup manifest and two proposed words required")
  man=json.loads(args.manifest.read_text());w=json.loads(args.words.read_text())
  if not isinstance(w,dict) or set(w)!={"C","D"}:raise ValueError("two original ATLAS generator mappings C,D required")
  lifts=man.get("normalizer_lifts",[])
  if len(lifts)!=2 or set(x.get("name") for x in lifts)!={"g3b","h3b"}:raise ValueError("not original mmgroup normalizer producer schema")
  gens={}
  for lift in lifts:
   lam=lift.get("central_image")
   if type(lam)!=int or lam not in (-1,1):raise ValueError("missing centre character")
   gens[lift["name"]]=(monster_matrix(lift),lam%3)
  targetC,phaseC=candidate_word(w["C"],gens)
  targetD,phaseD=candidate_word(w["D"],gens)
  if (phaseC,phaseD)!=(2,1):raise ValueError("centre-multiplier generator mismatch")
  result=check_pair((C,D),(targetC,targetD),actual_forms=True)
  result["monster_manifest_unmodified_source_authenticated_here"]=False
  result["supplied_quotient_word_correspondence_unproved"]=True
  result["word_lengths"]=[len(w["C"]),len(w["D"])]
  result["source_normalizer_generator_names"]=["g3b","h3b"]
 encoded=json.dumps(result,indent=2,sort_keys=True)+"\n"
 if args.out:args.out.write_text(encoded)
 print(encoded,end="")
if __name__=="__main__":main()
