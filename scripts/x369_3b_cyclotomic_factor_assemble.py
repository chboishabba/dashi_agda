"""Assemble complete actual characteristic-zero 90-column factor.

The normalized Weyl scalar is retained. Reduction gives a nonzero
determinant at 7; no modular semisimplicity or character identification
is used. Trace of a normalized factor is not yet a Suzuki character.
"""
import argparse
import json
from pathlib import Path
import numpy as np
from scripts.x369_3b_cyclotomic_rank import Q,ZERO
from scripts.x369_3b_cyclotomic_projector import digest
from scripts.monster_3b_mmgroup_checkpointed_weyl import read_pinned
from scripts.x369_actual_weyl_frame_bidi import require,inverse7


def assemble(mod,mod_sha,entries):
    require(mod['status']=='actual_MMV7_normalizer_tensor_factor'
            and mod['full_multiplicity_rank']==90 and len(mod['columns'])==90,'complete modular factor')
    require(len(entries)==90,'all 90 lifted columns required')
    cols=[];hashes=[];scope=None;phi=None
    for j,(r,sha) in enumerate(entries):
        c=r['contract']
        require(r['status']=='actual_cyclotomic_normalizer_column' and r['modular_reduction_agrees'] is True
                and r['cursor']==r['stages'] and c['seed']==j and c['modular_factor_sha256']==mod_sha,
                'actual lifted column scope')
        s={k:v for k,v in c.items() if k not in ('seed','seed_sha256')}
        if scope is None:scope=s;phi=r['reference_phi']
        require(s==scope and r['reference_phi']==phi,'inconsistent exact reference or source')
        col=[Q.wire(x) for x in r['coefficients']]
        require(len(col)==90 and [x.mod7() for x in col]==mod['columns'][j]['coefficients'],
                'actual reduced column changed')
        cols.append(col);hashes.append(sha)
    M=[list(row) for row in zip(*cols)]
    reduced=np.array([[v.mod7() for v in row] for row in M],dtype=np.int64)
    require(np.array_equal(reduced,np.array(mod['multiplicity_matrix'],dtype=np.int64)),'full modular matrix')
    require(np.array_equal(inverse7(reduced)@reduced%7,np.eye(90,dtype=np.int64)),'nonzero characteristic-zero determinant')
    require([Q.wire(x).mod7() for x in phi]==mod['reference_phi'],'actual Weyl normalization')
    tr=ZERO
    if scope['source_zeta']==scope['target_zeta']:
        for i in range(90):tr=tr+M[i][i]
    return dict(status='actual_cyclotomic_normalizer_factor',scope=scope,column_receipt_sha256=hashes,
        reference_phi=phi,multiplicity_matrix=[[v.pack() for v in row] for row in M],
        invertible_from_nonzero_mod7_minor=True,all_90_actual_columns_reduced=True,
        normalized_same_phase_trace=tr.pack() if scope['source_zeta']==scope['target_zeta'] else None,
        trace_is_character_of_linearized_6Suz=False,characteristic_zero_12_plus_78_certified=False)


class Entries:
    def __init__(self,root,rows):self.root=root;self.rows=rows
    def __len__(self):return len(self.rows)
    def __iter__(self):
        for r in self.rows:yield read_pinned(self.root/r['path'],r['sha256']),r['sha256']


def main():
    p=argparse.ArgumentParser()
    for k in ('modular-factor','column-manifest'):
        p.add_argument('--'+k,type=Path,required=True);p.add_argument('--'+k+'-sha256',required=True)
    p.add_argument('--output',type=Path,required=True);a=p.parse_args()
    m=read_pinned(a.modular_factor,a.modular_factor_sha256)
    entries=read_pinned(a.column_manifest,a.column_manifest_sha256)
    require(type(entries) is list,'ordered column receipt manifest')
    r=assemble(m,a.modular_factor_sha256,Entries(a.column_manifest.parent,entries))
    a.output.parent.mkdir(parents=True,exist_ok=True)
    with a.output.open('x') as f:json.dump(r,f,sort_keys=True,indent=2);f.write('\n')
    print(r['status'],digest(a.output.read_bytes()))

if __name__=='__main__':main()
