"""Actual quotient centralizer source: no character/order-based class guessing.

GAP computes a constructive centralizer and quotient conjugator in the
original pinned ATLAS matrix group. Returned free words are independently
replayed over F3. The actual MM lift and its E residual are separate.
"""
import argparse
import json
from pathlib import Path
import subprocess
import numpy as np
from scripts.x369_actual_3b_atlas_quotient_alignment import atlas_matrices,mm,inverse,I
from scripts.x369_3b_atlas_inverse_words import matrix_word
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_actual_weyl_frame_bidi import require
from scripts.x369_3b_cyclotomic_projector import digest

ROOT=Path(__file__).resolve().parents[1]


def run(a):
    r=read_pinned(a.alignment,a.alignment_sha256)
    require(r['status']=='actual_ATLAS_quotient_generator_alignment' and
        r['both_generated_quotient_groups_identified'] is True,'actual BIDI quotient alignment required')
    atlas=atlas_matrices(ROOT)
    h=[int(x) for x in a.representative.split(',') if x]
    g=[int(x) for x in a.word.split(',') if x] if a.word is not None else h
    H,T=matrix_word(h,atlas),matrix_word(g,atlas)
    A,B=[json.dumps(x.tolist()) for x in atlas]
    program=f"""
A:={A}*Z(3)^0;; B:={B}*Z(3)^0;;
G:=Group(A,B);;
H:={json.dumps(H.tolist())}*Z(3)^0;;
T:={json.dumps(T.tolist())}*Z(3)^0;;
F:=FreeGroup(2);;
hom:=GroupHomomorphismByImages(F,G,GeneratorsOfGroup(F),[A,B]);;
if hom=fail then Error("free word map unavailable"); fi;
q:=RepresentativeAction(G,T,H);;
if q=fail then
  Print("X369RESULT ",[0,Size(G)]," X369END\\n");
else
C:=Centralizer(G,H);;
gens:=GeneratorsOfGroup(C);;
W:=List(Concatenation([q^-1],gens),x->PreImagesRepresentative(hom,x));;
if fail in W then Error("constructive word lift unavailable"); fi;
if not ForAll([1..Length(W)],i->Image(hom,W[i])=Concatenation([q^-1],gens)[i]) then
  Error("source word verification");
fi;
if not T^q=H or not ForAll(gens,x->x*H=H*x) then Error("centralizer witness"); fi;
Print("X369RESULT ",[1,Size(G),Size(C),List(W,LetterRepAssocWord)]," X369END\\n");
fi;
QUIT;
"""
    base=dict(alignment_sha256=a.alignment_sha256,local_sha256=r['local_sha256'],
        representative=h,word=g,source_atlas_hashes=r['original_atlas_sha256'])
    try:
        p=subprocess.run([a.gap,'-q','-b'],input=program,text=True,capture_output=True,timeout=a.seconds)
    except subprocess.TimeoutExpired:
        return dict(base,status='bounded_quotient_centralizer_incomplete')
    require(p.returncode==0 and p.stdout.count('X369RESULT ')==1 and
        p.stdout.count(' X369END')==1,'GAP source computation did not finish: '+p.stderr[-2000:])
    data=json.loads(p.stdout.split('X369RESULT ',1)[1].split(' X369END',1)[0])
    if data[0]==0:
        return dict(base,status='source_GAP_quotient_nonconjugacy',quotient_order=data[1],
                    independently_verified_negative=False)
    _,order,size,words=data
    require(type(order) is int and type(size) is int and size>0 and order%size==0 and len(words)>=1,
            'source centralizer size')
    q=matrix_word(words[0],atlas)
    require(np.array_equal(mm(mm(q,T),inverse(q)),H),'independent quotient conjugator')
    for w in words[1:]:
        k=matrix_word(w,atlas)
        require(np.array_equal(mm(k,H),mm(H,k)),'independent centralizer generator check')
    return dict(base,status='source_GAP_quotient_centralizer',
        quotient_order=order,centralizer_order=size,quotient_class_size=order//size,
        left_conjugator=words[0],centralizer_words=words[1:],
        independent_matrix_word_checks=len(words),full_centralizer_computed_by_GAP=True,
        central_cover_class_identified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--alignment',type=Path,required=True);p.add_argument('--alignment-sha256',required=True)
    p.add_argument('--representative',required=True,help='comma-separated signed ATLAS generator indices (empty is identity)')
    p.add_argument('--word',help='optional second quotient word')
    p.add_argument('--gap',default='gap');p.add_argument('--seconds',type=float,default=80)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    require(0<a.seconds<=90,'bounded GAP source scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))
    if r['status']!='source_GAP_quotient_centralizer':raise SystemExit(2)

if __name__=='__main__':main()
