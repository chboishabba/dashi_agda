"""Actual Monster N(3B) -> ATLAS 2.Suz:2 generator-coordinate weld.

Original ATLAS GF3 matrices are pinned by their existing source owner.
Use exact E conjugation, not Monster character values, to identify a
candidate pair of source words in the literal 12-dimensional module.
The 13th coordinate retains the central correction. A quotient match
does not identify a 6.Suz cover lift or its character class.
"""
import argparse
import hashlib
import json
from pathlib import Path
from time import monotonic
import numpy as np
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_actual_3b_normalizer_tensor import source_coords
from scripts.x369_3b_nonzero_weyl_trace import make_word
from scripts.x369_actual_weyl_frame_bidi import require
from scripts.monster3b_atlas_actual_d4_word_witness import SOURCE_DIGESTS
from scripts.monster3b_atlas_source_word_order_d4_gate import parse_meataxe

N=12
I=np.eye(N,dtype=np.int64)
J=np.block([[np.zeros((6,6),dtype=np.int64),-np.eye(6,dtype=np.int64)],
            [np.eye(6,dtype=np.int64),np.zeros((6,6),dtype=np.int64)]])%3


def mm(a,b):return a@b%3


def pow3(a,n):
    x=np.eye(len(a),dtype=np.int64)
    while n:
        if n&1:x=mm(x,a)
        a=mm(a,a);n//=2
    return x


def rref(a):
    a=np.array(a,dtype=np.int64,copy=True)%3
    p=[];r=0
    for j in range(a.shape[1]):
        nz=np.flatnonzero(a[r:,j])
        if not len(nz):continue
        k=r+int(nz[0]);a[[r,k]]=a[[k,r]]
        a[r]=a[r]*int(a[r,j])%3
        for k in range(len(a)):
            if k!=r and a[k,j]:a[k]=(a[k]-a[k,j]*a[r])%3
        p.append(j);r+=1
        if r==len(a):break
    return a,p


def inverse(a):
    n=len(a);r,p=rref(np.concatenate((a,np.eye(n,dtype=np.int64)),axis=1))
    require(p[:n]==list(range(n)),'singular source coordinate matrix')
    return r[:,n:]


def nullspace(a):
    r,p=rref(a);n=r.shape[1];out=[]
    for j in range(n):
        if j in p:continue
        v=np.zeros(n,dtype=np.int64);v[j]=1
        for i,k in enumerate(p):v[k]=-r[i,j]%3
        out.append(v)
    return out


def intertwiner(actual,atlas):
    # Column convention: actual_i P = P atlas_i.
    cols=[]
    for j in range(N*N):
        e=np.zeros((N,N),dtype=np.int64);e.flat[j]=1
        cols.append(np.concatenate([(a@e-e@b).reshape(-1)%3 for a,b in zip(actual,atlas)]))
    ns=nullspace(np.stack(cols,axis=1))
    if len(ns)!=1:return None,len(ns)
    P=ns[0].reshape(N,N)
    if len(rref(P)[1])!=N:return None,1
    require(all(np.array_equal(mm(a,P),mm(P,b)) for a,b in zip(actual,atlas)),'intertwiner equation')
    return P,1


def log_coord(c):
    a,b,t=c
    return np.array((*a,*b,(t-2*sum(x*y for x,y in zip(a,b)))%3),dtype=np.int64)


def group_coord(v):
    a=tuple(map(int,v[:6]));b=tuple(map(int,v[6:12]))
    return a,b,(int(v[12])+2*sum(x*y for x,y in zip(a,b)))%3


def source_action(h,z,A,B):
    # Left conjugation is an honest column-matrix action.
    images=[source_coords(h*g*h**-1,z,A,B) for g in (*A,*B,z)]
    L=np.stack([log_coord(c) for c in images],axis=1)
    S=L[:12,:12];s=int(L[12,12])
    require(s in (1,2) and not np.any(L[:12,12]) and
            np.array_equal(mm(mm(S.T,J),S),s*J%3),'source symplectic similitude')
    require(len(rref(L)[1])==13,'actual automorphism inverse')
    return L


def inner_offset(L):
    # For identity quotient, conjugation by (a,b,t) adds
    # b dot x - a dot y to the central coordinate.
    require(np.array_equal(L[:12,:12],I) and L[12,12]==1 and not np.any(L[:12,12]),'not an inner action')
    row=L[12,:12]
    return tuple(int(-v%3) for v in row[6:]),tuple(map(int,row[:6])),0


def recover_coset(g,h,z,A,B):
    """Check a literal quotient collision, retain exact E and center."""
    k=g*h**-1
    L=source_action(k,z,A,B)
    c=inner_offset(L);e=make_word(c,z,A,B)
    t=next((i for i in range(3) if k==e*z**i),None)
    require(t is not None,'centralizer residual outside selected E: no quotient promotion')
    return (*c[:2],t)


def atlas_matrices(root):
    data=root/'data'/'atlas';out=[]
    for name,sha in SOURCE_DIGESTS.items():
        p=data/name
        require(hashlib.sha256(p.read_bytes()).hexdigest()==sha,'original ATLAS byte identity')
        out.append(np.array(parse_meataxe(p),dtype=np.int64))
    require(len(out)==2,'original two generators')
    return out


def evaluate(word,words,one):
    g=one
    for name in word:
        require(name.lstrip('-') in words and name.count('-')<=1,'literal word letter')
        x=words[name.lstrip('-')]
        g=g*(x**-1 if name.startswith('-') else x)
    return g


def run(a):
    from mmgroup import MM
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256);m=local['actual_local_sources']['ternary_manifest']
    checked=check_words(m)
    z=MM(m['center_word']);A=[MM(x) for x in m['translation_words']];B=[MM(x) for x in m['modulation_words']]
    words={r['name']:MM(r['word']) for r in m['normalizer_lifts']}
    atlas=atlas_matrices(Path(__file__).resolve().parents[1])
    # Candidate C,D words are explicit source inputs. Do not replace
    # a failure by a dimension/order coincidence.
    cw=a.c.split(',');dw=a.d.split(',')
    C,D=[evaluate(w,words,MM(1)) for w in (cw,dw)]
    L=[source_action(g,z,A,B) for g in (C,D)]
    P,dim=intertwiner([x[:12,:12] for x in L],atlas)
    out=dict(status='actual_ATLAS_quotient_generator_alignment' if P is not None else 'candidate_not_certified',
        local_sha256=a.local_sha256,manifest_sha256=checked['manifest_sha256'],
        original_atlas_sha256=SOURCE_DIGESTS,word_pair=[cw,dw],literal_words=[str(C),str(D)],
        automorphism_matrices=[x.tolist() for x in L],intertwiner_kernel_dimension=dim,
        actual_quotient_intertwiner=None,atlas_class_map_certified=False,six_suz_cover_lift_certified=False)
    if P is None:return out
    Pi=inverse(P)
    require(np.array_equal(mm(P,Pi),I),'coordinate inverse')
    out.update(actual_quotient_intertwiner=P.tolist(),inverse=Pi.tolist(),transport_checks=2,
               transported_alternating_form=mm(mm(P.T,J),P).tolist())
    # Literal representative/conjugator words are optional. Verify
    # a supplied quotient conjugation by actual source multiplication,
    # and recover the entire E discrepancy, not just its phase.
    if a.conjugacy:
        r=read_pinned(a.conjugacy,a.conjugacy_sha256)
        require(monotonic()<deadline,'actual conjugacy budget')
        w={'C':C,'D':D}
        g,h,k=[evaluate(r[x],w,MM(1)) for x in ('word','representative','conjugator')]
        moved=k*g*k**-1
        e=recover_coset(moved,h,z,A,B)
        out['literal_quotient_conjugacy']=dict(word=str(g),representative=str(h),conjugator=str(k),
            extraspecial_residual=e,actual_group_conjugacy=(moved==h),
            full_cover_class_identified=False)
    return out


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--c',required=True);p.add_argument('--d',required=True)
    p.add_argument('--conjugacy',type=Path);p.add_argument('--conjugacy-sha256')
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();require(0<a.seconds<=90 and bool(a.conjugacy)==bool(a.conjugacy_sha256),'bounded scope')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(r['status'])
    if r['status']!='actual_ATLAS_quotient_generator_alignment':raise SystemExit(2)

if __name__=='__main__':main()
