#!/usr/bin/env python3
"""Train an independently labelled per-prefix physical probe for TESSERA.

The input .npz contains actual precomputed (N,128) embeddings, a real-valued
(N,M) label matrix and cell/year/source ids. This program NEVER calls a
satellite prediction 'ground truth' without independent label provenance.
All scaling and ridge fitting use the training fold; spatial and year leakage
are prohibited. Output is a portable linear decoder; attach it to actual
differentiable TESSERA inference to obtain d(physical prediction)/d(sensor).
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
from sklearn.linear_model import Ridge
from sklearn.metrics import mean_absolute_error, mean_squared_error, r2_score

PREFIXES=(16,32,64,128)


def prepare(data, test_cells, test_years):
    required={'tessera','labels','cell','year','label_source'}
    if required-set(data):
        raise ValueError(f"missing independently labelled arrays: {required-set(data)}")
    v=np.asarray(data['tessera'],dtype=float)
    y=np.asarray(data['labels'],dtype=float)
    if y.ndim == 1: y=y[:,None]
    n=len(v)
    if v.shape!=(n,128) or y.shape[0]!=n or not np.isfinite(v).all() or not np.isfinite(y).all():
        raise ValueError('shape/finite validation failed')
    cells=np.asarray(data['cell']).astype(str);years=np.asarray(data['year']).astype(str)
    sources=np.asarray(data['label_source']).astype(str)
    if any(not s.strip() for s in sources) or any(not s.strip() for s in cells):
        raise ValueError('missing independent source or spatial identity')
    if len(set(zip(cells,years)))!=n:
        raise ValueError('duplicate cell/year')
    te=np.isin(cells,test_cells)&np.isin(years,[str(yr) for yr in test_years])
    tr=~np.isin(cells,test_cells)&~np.isin(years,[str(yr) for yr in test_years])
    if tr.sum()<3 or te.sum()<2:
        raise ValueError('insufficient disjoint train/test points')
    if (set(cells[tr])&set(cells[te])) or (set(years[tr])&set(years[te])):
        raise AssertionError('train/test spatial or temporal contamination')
    return v,y,tr,te,{'train_rows':int(tr.sum()),'test_rows':int(te.sum()),
      'train_cells':sorted(set(cells[tr])),'test_cells':sorted(set(cells[te])),
      'train_years':sorted(set(years[tr])),'test_years':sorted(set(years[te]))}


def train_prefix(v,y,tr,te,k,alpha=1.0):
    if k not in PREFIXES or alpha<=0: raise ValueError('bad prefix or alpha')
    x=v[:,:k]
    mean=x[tr].mean(axis=0); std=x[tr].std(axis=0)
    std[std==0]=1
    reg=Ridge(alpha=alpha).fit((x[tr]-mean)/std,y[tr])
    pred=np.asarray(reg.predict((x[te]-mean)/std)).reshape(-1,y.shape[1])
    W=np.asarray(reg.coef_).reshape(y.shape[1],k)
    b=np.asarray(reg.intercept_).reshape(y.shape[1])
    return {'mean':mean,'scale':std,'weight':W,'bias':b},{
      'MAE':float(mean_absolute_error(y[te],pred)),
      'RMSE':float(np.sqrt(mean_squared_error(y[te],pred))),
      'R2_uniform':float(r2_score(y[te],pred,multioutput='uniform_average')),
      'test_rows':int(te.sum())}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('matched_npz')
    p.add_argument('output_dir')
    p.add_argument('--test-cell',action='append',required=True)
    p.add_argument('--test-year',action='append',required=True)
    p.add_argument('--alpha',type=float,default=1.)
    p.add_argument('--target-name',required=True)
    p.add_argument('--target-unit',required=True)
    p.add_argument('--label-provenance',required=True)
    p.add_argument('--checkpoint-sha256',required=True)
    args=p.parse_args()
    with np.load(args.matched_npz,allow_pickle=False) as npz:
        data={k:npz[k] for k in npz.files}
    v,y,tr,te,split=prepare(data,args.test_cell,args.test_year)
    output=Path(args.output_dir);output.mkdir(parents=True,exist_ok=True)
    receipt={'target':args.target_name,'unit':args.target_unit,
       'label_provenance':args.label_provenance,
       'tessera_checkpoint_sha256':args.checkpoint_sha256,
       'dataset_sha256':hashlib.sha256(Path(args.matched_npz).read_bytes()).hexdigest(),
       'split':split,'heads':{},
       'limitation':'A heldout regression is not causal explanation or universal validation.'}
    for k in PREFIXES:
        head,metrics=train_prefix(v,y,tr,te,k,args.alpha)
        np.savez(output/f'physical_probe_d{k}.npz',**head)
        receipt['heads'][str(k)]=metrics
    (output/'validation.json').write_text(json.dumps(receipt,indent=2)+'\n')


if __name__=='__main__':
    main()
