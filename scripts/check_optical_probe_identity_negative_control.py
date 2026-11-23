"""OL3f: reject Fig 2a diffraction counts as an independent incident probe.

Real 2023 MOESM3 source workbook required. Purely diagnostic leakage counterexample;
never an accepted physical probe-to-detector reconstruction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.interpolate import RegularGridInterpolator
from check_optical_xlsx_ingest import sheets


def evaluate(path):
    data=sheets(path)
    measured=data['Fig 2f']; model=data['Fig 2g']; output=data['Fig 2a']
    freq=np.array([measured[1][j] for j in range(2,642)],float)
    delays=np.array([measured[i][0] for i in range(3,30)],float)
    Y=np.array([[measured[i][j] for j in range(2,642)] for i in range(3,30)],float)
    mf=np.array([model[1][j] for j in range(2,242)],float)*1e12
    mt=np.array([model[i][0] for i in range(3,64)],float)
    M=np.array([[model[i][j] for j in range(2,242)] for i in range(3,64)],float)
    Q=RegularGridInterpolator((mt,mf),M)(np.column_stack([np.repeat(delays,640),np.tile(freq,27)])).reshape(Y.shape)
    assert Y.shape==(27,640) and M.shape==(61,240)
    assert np.sum(Y<0)==4058
    xf=np.array([output[3][j] for j in range(1,256)],float)
    yf=np.array([output[4][j] for j in range(1,256)],float)
    assert output[1][0]=='Frequencies (THz)' and output[2][0]=='Counts (MHz)'
    assert output[3][0].startswith('Frequencies - smoothing')
    assert output[4][0].startswith('Counts - smoothing')
    assert np.all(np.diff(xf)>0)
    # This is a deliberately invalid proxy: measured diffraction counts are not
    # an independent probe spectrum; the test quantifies the resulting harm.
    proxy=np.interp(freq,xf,yf,left=0,right=0)
    order=np.argsort(delays); Y=Y[order];Q=Q[order]
    train=np.arange(27)%4!=0;train[[0,-1]]=True;test=~train
    assert train.sum()==21 and test.sum()==6
    def fit(T):
        a=np.column_stack([T[train].ravel(),np.ones(train.sum()*640)])
        c=np.linalg.lstsq(a,Y[train].ravel(),rcond=None)[0]
        return float(np.sqrt(np.mean((c[0]*T[test]+c[1]-Y[test])**2)))
    baseline=fit(Q)
    wrong_proxy=fit(Q*proxy[None,:])
    assert 9<baseline<11 and wrong_proxy>25
    q=sp.symbols('q',positive=True)
    assert sp.simplify((q*10**12)/10**12-q)==0
    return dict(source_sha256=hashlib.sha256(Path(path).read_bytes()).hexdigest(),
       original_workbook='2023 MOESM3',measured_map='Fig 2f',
       compared_model='Fig 2g',output_count_proxy='Fig 2a smoothed counts',
       measured_shape=list(Y.shape),proxy_range_thz=[float(xf.min()),float(xf.max())],
       proxy_supported_columns=int(np.count_nonzero(proxy)),map_columns=640,
       withheld_rows=int(test.sum()),baseline_global_gain_offset_rmse_mhz=baseline,
       invalid_proxy_rmse_mhz=wrong_proxy,
       finding='Fig 2a measured diffraction counts are not independently calibrated probe input; this proxy is physically invalid',
       original_incident_probe_spectrum_available=False,
       physical_model_acceptance=False)


def main():
    p=argparse.ArgumentParser();p.add_argument('moesm3');p.add_argument('--receipt');args=p.parse_args()
    r=evaluate(args.moesm3);s=json.dumps(r,indent=2,sort_keys=True)+'\n'
    if args.receipt:Path(args.receipt).write_text(s)
    print(s);print('PASS original-source output-vs-input identity negative control; SymPy',sp.__version__)


if __name__=='__main__':main()
