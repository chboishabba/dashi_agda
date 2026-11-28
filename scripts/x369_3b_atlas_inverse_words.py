"""Reverse actual quotient generators into the pinned ATLAS generator words.

GAP constructive membership is a source-dependent computation, not a
character-table fusion. All returned words are independently evaluated
over F3. The actual MM extraspecial residual is checked by the original
alignment producer on a second pass. No 6.Suz cover lift is inferred.
"""
import argparse
import json
from pathlib import Path
import subprocess
import numpy as np
from scripts.x369_actual_3b_atlas_quotient_alignment import atlas_matrices,mm,inverse,I
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_actual_weyl_frame_bidi import require
from scripts.x369_3b_cyclotomic_projector import digest


def matrix_word(letters,atlas):
    G=[None,*atlas];inv=[None,*[inverse(g) for g in atlas]]
    out=I
    for i in letters:
        require(type(i) is int and i in (-2,-1,1,2),'actual GAP free-group letter')
        out=mm(out,G[i] if i>0 else inv[-i])
    return out


def run(a):
    r=read_pinned(a.alignment,a.alignment_sha256)
    require(r['status']=='actual_ATLAS_quotient_generator_alignment','actual quotient alignment required')
    P=np.array(r['actual_quotient_intertwiner'],dtype=np.int64);Pi=inverse(P)
    atlas=atlas_matrices(Path(__file__).resolve().parents[1])
    names=sorted(r['actual_normalizer_quotient_matrices'])
    require(names==['g3b','h3b'],'actual original normalizer generator inventory')
    targets=[mm(mm(Pi,np.array(r['actual_normalizer_quotient_matrices'][n],dtype=np.int64)),P) for n in names]
    # Only exact integers enter the GAP program; no receipt strings as code.
    A,B=[json.dumps(g.tolist()) for g in atlas]
    T=json.dumps([t.tolist() for t in targets])
    program=f"""
A:={A}*Z(3)^0;; B:={B}*Z(3)^0;;
G:=Group(A,B);;
F:=FreeGroup(2);;
hom:=GroupHomomorphismByImages(F,G,GeneratorsOfGroup(F),[A,B]);;
if hom=fail then Error("actual free-group epimorphism unavailable"); fi;
T:=List({T},x->x*Z(3)^0);;
if not ForAll(T,x->x in G) then Error("actual quotient membership failed"); fi;
W:=List(T,x->PreImagesRepresentative(hom,x));;
if fail in W then Error("constructive membership unavailable"); fi;
if not ForAll([1..Length(T)],i->Image(hom,W[i])=T[i]) then Error("word evaluation failed"); fi;
Print("X369WORDS ",List(W,LetterRepAssocWord)," X369END\\n");
QUIT;
"""
    try:p=subprocess.run([a.gap,'-q','-b'],input=program,text=True,capture_output=True,timeout=a.seconds)
    except subprocess.TimeoutExpired:return dict(status='bounded_inverse_word_search_incomplete',alignment_sha256=a.alignment_sha256)
    require(p.returncode==0 and p.stdout.count('X369WORDS ')==1 and p.stdout.count(' X369END')==1,
            'GAP constructive word search failed: '+p.stderr[-2000:])
    words=json.loads(p.stdout.split('X369WORDS ',1)[1].split(' X369END',1)[0])
    require(len(words)==len(names),'actual inverse word count')
    out={}
    for n,w,t in zip(names,words,targets):
        require(np.array_equal(matrix_word(w,atlas),t),'independent exact matrix word verification')
        out[n]=[('' if i>0 else '-')+('C' if abs(i)==1 else 'D') for i in w]
    return dict(status='ATLAS_quotient_inverse_word_witness',alignment_sha256=a.alignment_sha256,
        local_sha256=r['local_sha256'],actual_word_pair=r['word_pair'],inverse_words=out,
        actual_quotient_matrix_word_checks=len(out),actual_MM_residual_reopened=False,
        six_suz_cover_lift_certified=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('--alignment',type=Path,required=True);p.add_argument('--alignment-sha256',required=True)
    p.add_argument('--gap',default='gap');p.add_argument('--seconds',type=float,default=80)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args();require(0<a.seconds<=90,'bounded GAP scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))
    if r['status']!='ATLAS_quotient_inverse_word_witness':raise SystemExit(2)

if __name__=='__main__':main()
