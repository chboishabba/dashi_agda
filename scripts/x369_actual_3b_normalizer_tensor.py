"""Actual 3B normalizer tensor-factor transport over F7.

Given both rank90 actual phase frames, factor the literal normalizer
action into a 729-dimensional Weyl operator and a 90-dimensional
multiplicity operator. Retain the projective scalar normalization.
This is a modular source intertwiner, not the characteristic-zero
Suzuki 12+78 character identification (7 divides the group order).
"""
import argparse
import hashlib
import json
from itertools import product
from pathlib import Path
from time import monotonic
import numpy as np
from scripts.x369_actual_weyl_frame_bidi import WeylFrame,RowBasis,source_sha,inverse7,require
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words

WEIGHTS=tuple(product(range(3),repeat=6))
POSITIONS=np.array(WEIGHTS,dtype=np.int64)
RADIX=np.array([243,81,27,9,3,1],dtype=np.int64)
ZERO=(0,)*6


def monomial(v,coord,zeta):
    """Right action A^a B^b z^t on a Weyl-weight column."""
    a,b,t=coord
    dst=(POSITIONS-np.array(a))%3
    index=dst@RADIX
    phase=(dst@np.array(b)+t)%3
    out=np.zeros(729,dtype=np.int64)
    out[index]=(np.array(v,dtype=np.int64)*np.array([1,zeta,zeta*zeta%7])[phase])%7
    return out


def fixed_line(modulations,zeta):
    """Construct the unique common fixed line by exact averaging."""
    for i in range(729):
        w=np.zeros(729,dtype=np.int64);w[i]=1
        for b in modulations:
            t=monomial(w,b,zeta)
            w=5*(w+t+monomial(t,b,zeta))%7
            if not np.any(w):break
        nz=np.flatnonzero(w)
        if len(nz):
            k=int(nz[0]);w=w*pow(int(w[k]),-1,7)%7
            require(all(np.array_equal(monomial(w,b,zeta),w) for b in modulations),
                    'reference fixed line')
            return WEIGHTS[k],w
    raise ValueError('no normalized reference fixed line')


def source_coords(g,z,A,B):
    def comm(x,y):
        for t in range(3):
            if x*y==z**t*y*x:return t
        raise ValueError('normalizer image outside actual extraspecial group')
    a=tuple(-comm(g,b)%3 for b in B)
    b=tuple(comm(g,x) for x in A)
    w=z**0
    for x,k in zip(A,a):w=w*x**k
    for x,k in zip(B,b):w=w*x**k
    for t in range(3):
        if g==w*z**t:return a,b,t
    raise ValueError('actual source coordinate inverse')


def reopen_frame(r,manifest,local_sha,manifest_sha,zeta):
    from mmgroup import MM,MMV
    from importlib.metadata import version
    c=r['contract']
    require(c['local_receipt_sha256']==local_sha and c['manifest_sha256']==manifest_sha
            and c['mmgroup_version']==version('mmgroup') and c['zeta']==zeta and c['modulus']==7
            and r['status']=='actual_MMV7_ternary_weyl_basis'
            and r['verified_seed_count']==90 and r['actual_weight_checks']==3240
            and r['actual_two_weight_bidi'] is True,'complete actual phase-frame receipt required')
    z=MM(manifest['center_word']);A=tuple(MM(x) for x in manifest['translation_words'])
    B=tuple(MM(x) for x in manifest['modulation_words'])
    f=WeylFrame(3,zeta,z,A,B,[],[],RowBasis());V=MMV(7)
    for label,expected in zip(r['seed_labels'],r['seed_sha256'],strict=True):
        require(f.admit(V(*label),label) and source_sha(f.seeds[-1])==expected,'actual seed source inverse')
    require(len(f.seeds)==90 and f.rank.pivots==r['pivot_indices'],'actual source frame changed')
    return f


def digest(raw):return hashlib.sha256(raw).hexdigest()


def run(a):
    from mmgroup import MM
    require(0<a.seconds<=90 and bool(a.resume)==bool(a.resume_sha256),'bounded source scope')
    local=read_pinned(a.local,a.local_sha256)
    m=local['actual_local_sources']['ternary_manifest'];source=check_words(m)
    entry=next((g for g in m['normalizer_lifts'] if g['name']==a.lift),None)
    require(entry is not None,'unknown actual normalizer lift')
    source_zeta=a.zeta;target_zeta=pow(source_zeta,entry['central_image']%3,7)
    left=reopen_frame(read_pinned(a.frame,a.frame_sha256),m,a.local_sha256,
                      source['manifest_sha256'],source_zeta)
    if target_zeta==source_zeta:
        require(a.target is None and a.target_sha256 is None,'same phase uses same retained frame')
        right=left;target_sha=a.frame_sha256
    else:
        require(a.target is not None and a.target_sha256 is not None,'actual opposite phase frame required')
        right=reopen_frame(read_pinned(a.target,a.target_sha256),m,a.local_sha256,
                           source['manifest_sha256'],target_zeta)
        target_sha=a.target_sha256
    h=MM(entry['word']);z=left.center;A=left.A;B=left.B
    require(h**-1*z*h==z**(entry['central_image']%3),'actual central phase')
    invh=h**-1
    # If v has source weight zero, v*h is fixed by h^-1 B_i h.
    aa=[source_coords(invh*g*h,z,A,B) for g in A]
    bb=[source_coords(invh*g*h,z,A,B) for g in B]
    weight,phi=fixed_line(bb,target_zeta)
    support=np.flatnonzero(phi)
    other=WEIGHTS[int(support[-1])] if len(support)>1 else next(u for u in WEIGHTS if u!=weight)
    other_coeff=int(phi[WEIGHTS.index(other)])
    inv=right.pivot_inverse()
    contract=dict(local_sha256=a.local_sha256,frame_sha256=a.frame_sha256,target_sha256=target_sha,
        source_zeta=source_zeta,target_zeta=target_zeta,lift=a.lift,word=entry['word'],
        source_manifest_sha256=source['manifest_sha256'],
        implementation_sha256=digest(Path(__file__).read_bytes()),
        weyl_frame_sha256=digest(Path(__file__).with_name('x369_actual_weyl_frame_bidi.py').read_bytes()))
    rows=[]
    if a.resume:
        r=read_pinned(a.resume,a.resume_sha256)
        require(r['contract']==contract and r['status']=='bounded_incomplete','normalizer scope changed')
        require(r['reference_phi']==phi.tolist() and tuple(r['normalization_weight'])==weight,
                'reference factor changed')
        rows=r['columns']
        require([r['j'] for r in rows]==list(range(len(rows))) and len(rows)<=90,
                'noncontiguous columns')
    deadline=monotonic()+a.seconds
    for j in range(len(rows),90):
        if monotonic()>=deadline:break
        w=left.seeds[j]*h
        require(w*z==target_zeta*w and w*invh==left.seeds[j],'actual normalizer inverse')
        c=right.read_weight(w,weight,inv)
        d=right.read_weight(w,other,inv)
        require(d==tuple(other_coeff*x%7 for x in c),'actual Weyl factor at independent weight')
        # One actual translated source seed, checked through its own
        # conjugated A image and independently constructed reference.
        u=(1,0,0,0,0,0)
        v=left.column(u,j)*h
        a0,b0,t0=aa[0]
        # inverse A-image via source group, not by a guessed sign.
        inverse_coord=source_coords((invh*A[0]*h)**-1,z,A,B)
        f=monomial(phi,inverse_coord,target_zeta)
        k=int(np.flatnonzero(f)[0])
        require(right.read_weight(v,WEIGHTS[k],inv)==tuple(int(f[k])*x%7 for x in c),
                'actual translated normalizer column')
        rows.append(dict(j=j,coefficients=list(c),independent_weight_checked=True,
                         translated_source_weight_checked=True))
    complete=len(rows)==90
    matrix=None;inverse=None
    if complete:
        matrix=np.array([r['coefficients'] for r in rows],dtype=np.int64).T
        inverse=inverse7(matrix)
        require(np.array_equal(matrix@inverse%7,np.eye(90,dtype=np.int64)),'multiplicity inverse')
    return dict(status='actual_MMV7_normalizer_tensor_factor' if complete else 'bounded_incomplete',
        contract=contract,parent_receipt_sha256=a.resume_sha256,
        reference_phi=phi.tolist(),normalization_weight=weight,normalization_coefficient=1,
        transformed_translation_coordinates=aa,transformed_modulation_coordinates=bb,
        reference_weight_basis_dimension=729,columns=rows,
        multiplicity_matrix=None if matrix is None else matrix.tolist(),
        multiplicity_inverse=None if inverse is None else inverse.tolist(),
        full_multiplicity_rank=90 if complete else None,
        actual_normalizer_factorization_from_weyl_covariance=complete,
        modular_projective_scalar_normalization_retained=True,
        characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    p.add_argument('--local',type=Path,required=True);p.add_argument('--local-sha256',required=True)
    p.add_argument('--frame',type=Path,required=True);p.add_argument('--frame-sha256',required=True)
    p.add_argument('--target',type=Path);p.add_argument('--target-sha256')
    p.add_argument('--zeta',type=int,choices=(2,4),default=2)
    p.add_argument('--lift',required=True);p.add_argument('--seconds',type=float,default=80)
    p.add_argument('--resume',type=Path);p.add_argument('--resume-sha256')
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    if a.output.exists():raise FileExistsError(a.output)
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],len(r['columns']),digest(a.output.read_bytes()))
    if r['status']=='bounded_incomplete':raise SystemExit(2)

if __name__=='__main__':main()
