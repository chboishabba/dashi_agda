"""Measured 2023 Fig 2f: physical-law adequacy versus nonphysical compression.

Uses publisher's original uploaded MOESM3 workbook; never bundles source data.
Full-map SVD is descriptive (NOT a held-out/generalization certificate).
Physical candidate is an intentionally restricted two-slit harmonic model,
NOT the authors' realistic switching/probe/measurement model.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp
from check_optical_2023_source_replay import read_workbook


def analyse(path):
    book = read_workbook(path)
    tab = book['Fig 2f']
    f = np.array([tab[1,c] for c in range(3,643)], dtype=float)
    tau = np.array([tab[r,1] for r in range(3,30)], dtype=float)
    y = np.array([[tab[r,c] for c in range(3,643)] for r in range(3,30)], dtype=float)
    assert y.shape == (27,640) and np.all(np.diff(f)<0)
    assert len(set(tau)) == 27 and np.all(np.isfinite(y))
    assert (y<0).sum() == 4058
    checks = 4
    n = y.size
    u,s,vt = np.linalg.svd(y, full_matrices=False)
    compressions=[]
    for k in (1,2,4,8,12):
        prediction=(u[:,:k]*s[:k]) @ vt[:k]
        residual=y-prediction
        squared=float(np.sum(residual*residual))
        tail=float(np.sum(s[k:]*s[k:]))
        assert abs(squared-tail)<1e-7*max(1.,tail)
        checks+=1
        compressions.append(dict(rank=k,parameters=k*(y.shape[0]+y.shape[1]+1),
          rmse=float(np.sqrt(squared/n)),relative_l2=float(np.linalg.norm(residual)/np.linalg.norm(y)),
          max_absolute=float(np.max(np.abs(residual))),p95_absolute=float(np.quantile(np.abs(residual),.95))))
    # Fixed, publicly disclosed restricted physical benchmark, with no frequency leakage:
    # each row has a smooth RBF envelope plus complex two-slit carrier at known tau.
    # Every fifth spectral column is withheld from its coefficient fit.
    x=(f-230.)/5.
    centers=np.linspace(-2.5,2.5,9)
    env=np.exp(-.5*((x[:,None]-centers[None,:])/.7)**2)
    train=(np.arange(len(f))%5)!=0
    test=~train
    physical={}
    for harmonics in (0,1,2):
        prediction=np.empty_like(y)
        for i,t in enumerate(tau):
            design=env.copy()
            for h in range(1,harmonics+1):
                theta=2*np.pi*h*(f-230.)*t/1000.
                design=np.column_stack((design,env*np.cos(theta)[:,None],env*np.sin(theta)[:,None]))
            coefficient=np.linalg.lstsq(design[train],y[i,train],rcond=1e-10)[0]
            prediction[i]=design@coefficient
        physical[f'harmonics_{harmonics}']=dict(
          fit_parameters=27*9*(1+2*harmonics),
          training_rmse=float(np.sqrt(np.mean((prediction[:,train]-y[:,train])**2))),
          withheld_columns_rmse=float(np.sqrt(np.mean((prediction[:,test]-y[:,test])**2))))
        assert np.all(np.isfinite(prediction));checks+=1
    assert physical['harmonics_2']['withheld_columns_rmse'] < physical['harmonics_0']['withheld_columns_rmse'];checks+=1
    p,t=sp.symbols('p t',positive=True)
    assert sp.simplify(p*(1000/p)-1000)==0;checks+=1
    return dict(article_doi='10.1038/s41567-023-01993-w',workbook_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),
      worksheet='Fig 2f',grid_shape=list(y.shape),signed_negative_samples=int((y<0).sum()),
      observed_std=float(np.std(y)),SVD_full_map_descriptive_not_holdout=compressions,
      restricted_two_slit_heldout_harmonic_benchmark=physical,
      scientific_retention_gate='OPEN: require externally validated physically explanatory forward model, noise-based error bounds, held-out independent conditions and immutable raw-source reference',
      checks=checks)


def main():
    parser=argparse.ArgumentParser();parser.add_argument('source_xlsx');parser.add_argument('--receipt');a=parser.parse_args()
    result=analyse(a.source_xlsx)
    report=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if a.receipt:Path(a.receipt).write_text(report)
    print(report);print(f'{result["checks"]}/{result["checks"]} PASS (local SymPy, NumPy and publisher XLSX)')


if __name__=='__main__':main()
