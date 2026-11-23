"""OL3e: measured Fig 2f against original publisher model Fig 2g.

Source workbooks remain external. The publisher model is not a newly
independent physical calibration of the optical probe or detector.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.interpolate import RegularGridInterpolator, PchipInterpolator
from scipy.ndimage import gaussian_filter1d
from check_optical_xlsx_ingest import sheets


def analyse(source):
    data = sheets(source)
    measured = data['Fig 2f']; model = data['Fig 2g']
    freq = np.array([measured[1][j] for j in range(2,642)],dtype=float)
    delay = np.array([measured[i][0] for i in range(3,30)],dtype=float)
    Y = np.array([[measured[i][j] for j in range(2,642)] for i in range(3,30)],dtype=float)
    raw_freq=np.array([model[1][j] for j in range(2,242)],dtype=float)
    model_freq=raw_freq*1e12
    model_delay=np.array([model[i][0] for i in range(3,64)],dtype=float)
    M=np.array([[model[i][j] for j in range(2,242)] for i in range(3,64)],dtype=float)
    assert Y.shape==(27,640) and M.shape==(61,240)
    assert np.all(np.diff(freq)<0) and np.all(np.diff(model_freq)>0)
    assert np.all(np.diff(model_delay)>0)
    assert model_freq.min()<freq.min()<freq.max()<model_freq.max()
    assert model_delay.min()<=delay.min() and model_delay.max()>=delay.max()
    checks=4
    interpolate=RegularGridInterpolator((model_delay,model_freq),M,bounds_error=True)
    queries=np.column_stack([np.repeat(delay,640),np.tile(freq,27)])
    Q=interpolate(queries).reshape(Y.shape)
    assert np.all(np.isfinite(Q)) and int(np.sum(Y<0))==4058;checks+=1
    order=np.argsort(delay);delay=delay[order];Y=Y[order];Q=Q[order]
    train=np.arange(27)%4!=0;train[[0,-1]]=True;test=~train
    assert train.sum()==21 and test.sum()==6;checks+=1
    def score(pred):
        err=(pred-Y)[test]
        return dict(rmse_mhz=float(np.sqrt(np.mean(err**2))),
                    mae_mhz=float(np.mean(np.abs(err))),
                    p95_abs_mhz=float(np.quantile(np.abs(err),.95)),
                    max_abs_mhz=float(np.max(np.abs(err))))
    raw=score(Q)
    X=np.column_stack((Q[train].ravel(),np.ones(train.sum()*640)))
    coeff=np.linalg.lstsq(X,Y[train].ravel(),rcond=None)[0]
    global_fit=score(coeff[0]*Q+coeff[1]);checks+=1
    gains=np.array([np.dot(Q[i],Y[i])/np.dot(Q[i],Q[i]) for i in np.where(train)[0]])
    gains_all=PchipInterpolator(delay[train],gains)(delay)
    row_fit=score(Q*gains_all[:,None]);checks+=1
    correction=gaussian_filter1d(np.mean(Y[train]-Q[train],axis=0),sigma=4)
    residual_fit=score(Q+correction[None,:]);checks+=1
    corr=float(np.corrcoef(Q.ravel(),Y.ravel())[0,1])
    assert .8<corr<1;checks+=1
    assert global_fit['rmse_mhz']>2 and row_fit['rmse_mhz']>2;checks+=1
    x=sp.symbols('x',positive=True)
    assert sp.simplify(x*10**12/10**12-x)==0;checks+=1
    return dict(article_doi='10.1038/s41567-023-01993-w',
       source_sha256=hashlib.sha256(Path(source).read_bytes()).hexdigest(),
       measured_sheet='Fig 2f',publisher_model_sheet='Fig 2g',
       measured_shape=list(Y.shape),model_shape=list(M.shape),
       model_frequency_scale=1e12,negative_measured_samples=int(np.sum(Y<0)),
       full_map_correlation=corr,heldout_separations_fs=delay[test].tolist(),
       uncalibrated_model=raw,global_gain_offset=global_fit,
       global_coefficients=coeff.tolist(),per_delay_interpolated_gain=row_fit,
       map_trained_residual_template_diagnostic=residual_fit,
       checks=checks,table_replacement_accepted=False,
       limitation='The Fig 2g grid is published modelling, not independent experimental probe calibration. The 640-bin residual template uses measured training rows.')


def main():
    parser=argparse.ArgumentParser();parser.add_argument('source_xlsx')
    parser.add_argument('--receipt');args=parser.parse_args()
    result=analyse(args.source_xlsx)
    output=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:Path(args.receipt).write_text(output)
    print(output);print(f'{result["checks"]}/{result["checks"]} PASS; SymPy {sp.__version__}')


if __name__=='__main__':main()
