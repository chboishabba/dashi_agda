"""Exact nonzero Weyl trace witness and source character normalization.

Barraclough--Wilson 2007 base1458 extension and existing 6.Suz source
selector own the ordinary characters. This module supplies the actual
normalized Weyl trace, including a constructive nonzero E-offset when
the unshifted trace vanishes. The offset has trivial Suzuki quotient.
No class number is guessed from order, trace, or a matching dimension.
"""
import argparse
import json
from pathlib import Path
from time import monotonic
from scripts.x369_3b_cyclotomic_rank import Q,ONE,ZERO,PHASE
from scripts.x369_3b_cyclotomic_normalizer import WEIGHTS,reference,sum_q
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_3b_cyclotomic_projector import digest
from scripts.x369_actual_weyl_frame_bidi import require

Z=(0,)*6
INDEX={u:i for i,u in enumerate(WEIGHTS)}


def dot(a,b):return sum(x*y for x,y in zip(a,b))%3


def mul_coord(x,y):
    a,b,t=x;c,d,s=y
    return tuple((i+j)%3 for i,j in zip(a,c)),tuple((i+j)%3 for i,j in zip(b,d)),(t+s+dot(b,c))%3


def inv_coord(x):
    a,b,t=x
    return tuple(-i%3 for i in a),tuple(-i%3 for i in b),(dot(a,b)-t)%3


def column_coords(aa):
    inv=[inv_coord(a) for a in aa];out=[]
    for u in WEIGHTS:
        g=(Z,Z,0)
        for a,k in zip(inv,u):
            for _ in range(k):g=mul_coord(g,a)
        out.append(g)
    return out


def coefficient(phi,c,row,phase):
    # Right monomial A^a B^b z^t sends input row+a to row.
    a,b,t=c
    src=tuple((x+y)%3 for x,y in zip(row,a))
    return phi[INDEX[src]]*PHASE[phase*(dot(row,b)+t)%3]


def diagonal(phi,cols,a,phase):
    # Diagonal of W followed by A^a. Modulation then contributes
    # omega^(phase*<u,b>) on its u-th diagonal entry.
    return [coefficient(phi,c,tuple((x+y)%3 for x,y in zip(u,a)),phase)
            for u,c in zip(WEIGHTS,cols)]


def fourier_line(values,b,phase):
    return sum_q(x*PHASE[phase*dot(u,b)%3] for u,x in zip(WEIGHTS,values))


def nonzero_trace(phi,aa,phase,deadline=None):
    require(len(phi)==729 and len(aa)==6 and phase in (1,2),'Weyl reference scope')
    cols=column_coords(aa)
    d0=diagonal(phi,cols,Z,phase)
    ordinary=sum_q(d0)
    if ordinary:return (Z,Z,0),ordinary,ordinary,1
    # Choose displacement so the zero-column's nonzero coefficient
    # becomes diagonal. Fourier invertibility guarantees a nonzero
    # coefficient among the 729 modulation choices.
    a=WEIGHTS[next(i for i,v in enumerate(phi) if v)]
    d=diagonal(phi,cols,a,phase)
    require(bool(d[0]),'constructive diagonal witness')
    for j,b in enumerate(WEIGHTS,1):
        if deadline is not None and monotonic()>=deadline:raise TimeoutError('trace witness budget')
        t=fourier_line(d,b,phase)
        if t:return (a,b,0),t,ordinary,j
    raise ValueError('nonzero diagonal contradicts exact Fourier invertibility')


def make_word(coord,z,A,B):
    a,b,t=coord;w=z**0
    for g,k in zip(A,a):w=w*g**k
    for g,k in zip(B,b):w=w*g**k
    return w*z**t


def run(a):
    from mmgroup import MM
    from scripts.monster_3b_mmgroup_weyl_word_alignment import check_words
    from scripts.x369_actual_3b_normalizer_tensor import source_coords
    deadline=monotonic()+a.seconds
    local=read_pinned(a.local,a.local_sha256)
    m=local['actual_local_sources']['ternary_manifest'];check=check_words(m)
    mod=read_pinned(a.modular_factor,a.modular_factor_sha256);c=mod['contract']
    f=read_pinned(a.factor,a.factor_sha256);s=f['scope']
    require(f['status']=='actual_cyclotomic_normalizer_factor' and f['all_90_actual_columns_reduced'] is True
            and s['modular_factor_sha256']==a.modular_factor_sha256 and c['local_sha256']==a.local_sha256
            and c['source_manifest_sha256']==check['manifest_sha256'] and s['source_zeta']==s['target_zeta']==c['source_zeta']==c['target_zeta'],
            'same-phase actual source factor required')
    h=MM(c['word']);z=MM(m['center_word']);A=[MM(w) for w in m['translation_words']]
    B=[MM(w) for w in m['modulation_words']]
    require(h*z==z*h,'actual phase-preserving word')
    aa=[source_coords(h**-1*g*h,z,A,B) for g in A]
    bb=[source_coords(h**-1*g*h,z,A,B) for g in B]
    phase=1 if s['source_zeta']==2 else 2
    phi=reference(bb,phase,c and mod['normalization_weight'])
    require([x.pack() for x in phi]==f['reference_phi'] and [x.mod7() for x in phi]==mod['reference_phi'],
            'actual exact normalized reference')
    coord,t,ordinary,n=nonzero_trace(phi,aa,phase,deadline)
    e=make_word(coord,z,A,B);w=h*e
    require(w*z==z*w,'phase-preserving offset')
    M=f['multiplicity_matrix'];require(len(M)==90 and all(len(r)==90 for r in M),'actual multiplicity scope')
    trace=sum_q(Q.wire(M[i][i]) for i in range(90))
    require(trace.pack()==f['normalized_same_phase_trace'],'actual source trace')
    return dict(status='actual_source_nonzero_Weyl_trace_witness',local_sha256=a.local_sha256,
        factor_sha256=a.factor_sha256,modular_factor_sha256=a.modular_factor_sha256,
        phase=phase,zeta=s['source_zeta'],word=str(h),offset_coordinates=coord,offset_word=str(e),
        offset_product_word=str(w),center_word=str(z),central_shift_words=[str(w*z**i) for i in range(3)],
        ordinary_normalized_Weyl_trace=ordinary.pack(),offset_normalized_Weyl_trace=t.pack(),
        normalized_multiplicity_trace=trace.pack(),normalized_full_phase_trace=(t*trace).pack(),
        modulation_candidates=n,offset_trivial_in_Suzuki_quotient_from_E_word=True,
        source_cover_class_identified=False,characteristic_zero_12_plus_78_certified=False)


def main():
    p=argparse.ArgumentParser()
    for k in ('local','factor','modular-factor'):
        p.add_argument('--'+k,type=Path,required=True);p.add_argument('--'+k+'-sha256',required=True)
    p.add_argument('--seconds',type=float,default=80);p.add_argument('--output',type=Path,required=True)
    a=p.parse_args();require(0<a.seconds<=90,'bounded source')
    r=run(a);a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,indent=2,sort_keys=True);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))

if __name__=='__main__':main()
