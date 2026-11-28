"""Exact E-conjugacy normal form in an actual N(3B) quotient coset.

Use the already aligned 13D class-two logarithm. A fixed quotient
representative h is NOT a full normalizer conjugacy class. The orbit
normal form here is only for conjugation by the extraspecial E.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from scripts.x369_actual_3b_atlas_quotient_alignment import (
    I,J,mm,rref,nullspace,log_coord,group_coord,source_action,recover_coset)
from scripts.x369_3b_nonzero_weyl_trace import make_word
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
from scripts.x369_actual_weyl_frame_bidi import require
from scripts.x369_3b_cyclotomic_projector import digest


def geometry(L):
    L=np.asarray(L,dtype=np.int64)%3
    require(L.shape==(13,13) and not np.any(L[:12,12]) and L[12,12] in (1,2),
            'actual class-two automorphism')
    S=L[:12,:12];s=int(L[12,12]);ell=L[12,:12]
    require(np.array_equal(mm(mm(S.T,J),S),s*J%3),'actual similitude')
    D=(I-S)%3;R,p=rref(D.T);basis=R[:len(p)]
    K=nullspace(D)
    return S,s,ell,D,basis,p,K


def solve(A,b):
    R,p=rref(np.column_stack((A,b)))
    n=A.shape[1]
    if n in p:return None
    x=np.zeros(n,dtype=np.int64)
    for i,j in enumerate(p):x[j]=R[i,n]
    require(np.array_equal(A@x%3,b%3),'exact source linear inverse')
    return x


def conjugate(L,e,x):
    # log(x e h x^-1 h^-1) = BCH(x,e,-Lx).
    u=L@x%3;v=x[:12];d=e[:12];w=u[:12]
    out=(x+e-u)%3
    out[12]=(out[12]+2*int(v@J@d-(v+d)@J@w))%3
    return out


def normal_form(L,e):
    S,s,ell,D,basis,p,K=geometry(L)
    e=np.asarray(e,dtype=np.int64)%3
    require(e.shape==(13,),'source coset logarithm')
    d=e[:12].copy()
    for row,j in zip(basis,p):d=(d-d[j]*row)%3
    v=solve(D,(d-e[:12])%3)
    require(v is not None,'quotient coset inverse')
    x=np.r_[v,0];q=conjugate(L,e,x)
    require(np.array_equal(q[:12],d),'canonical quotient displacement')
    # The stabilizer of d acts on its central fibre by a linear form.
    row=(-ell+J@d)%3
    shifts=[int(row@k)%3 for k in K]+[(1-s)%3]
    if any(shifts):
        j=next(i for i,t in enumerate(shifts) if t)
        y=np.r_[K[j],0] if j<len(K) else np.r_[np.zeros(12,dtype=np.int64),1]
        y=y*(-int(q[12])*shifts[j])%3
        r=conjugate(L,q,y)
        # Compose y x in E, not componentwise central addition.
        w=(y+x)%3;w[12]=(w[12]+2*int(y[:12]@J@x[:12]))%3
        require(r[12]==0 and np.array_equal(conjugate(L,e,w),r),'central fibre inverse')
        return r,w,False
    return q,x,True


def orbit_count(L):
    S,s,ell,D,basis,p,K=geometry(L)
    free=[i for i in range(12) if i not in p];k=len(free)
    require(k==len(K),'rank-nullity')
    if s!=1:return dict(quotient_dimension=k,split_displacements=0,E_orbits=3**k)
    # The central fibre is split exactly when (Jd-ell) vanishes on K.
    C=np.array([[int(v@J[:,i])%3 for i in free] for v in K],dtype=np.int64).reshape(k,k)
    b=np.array([int(v@ell)%3 for v in K],dtype=np.int64)
    r=len(rref(C)[1]);w=solve(C,b)
    split=0 if w is None else 3**(k-r)
    return dict(quotient_dimension=k,central_constraint_rank=r,split_displacements=split,
                E_orbits=3**k+2*split)


def run(a):
    from mmgroup import MM
    local=read_pinned(a.local,a.local_sha256);m=local['actual_local_sources']['ternary_manifest']
    checked=check_words(m);z=MM(m['center_word']);A=[MM(w) for w in m['translation_words']]
    B=[MM(w) for w in m['modulation_words']]
    h=MM(a.representative);g=MM(a.word)
    L=source_action(h,z,A,B);e=log_coord(recover_coset(g,h,z,A,B))
    q,x,split=normal_form(L,e)
    w=make_word(group_coord(x),z,A,B);rep=make_word(group_coord(q),z,A,B)*h
    require(w*g*w**-1==rep,'actual canonical coset conjugator')
    p,_,s=normal_form(L,q)
    require(np.array_equal(p,q) and s==split,'canonical section idempotent')
    return dict(status='actual_E_coset_conjugacy_normal_form',local_sha256=a.local_sha256,
        manifest_sha256=checked['manifest_sha256'],representative=str(h),source_word=str(g),
        normal_form_word=str(rep),literal_conjugator=str(w),normal_form_log=q.tolist(),
        central_fibre_split=split,coset_orbit_count=orbit_count(L),
        actual_conjugacy_verified=True,full_normalizer_class_identified=False,
        six_suz_cover_class_identified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--representative',required=True);p.add_argument('--word',required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))

if __name__=='__main__':main()
