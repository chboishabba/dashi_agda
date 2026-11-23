"""Original 2023 Fig 2e: measured fringe period versus slit separation.

Requires the authors' MOESM3 XLSX, no bundled experimental data. This is an
intensity-derived period check, not complex-field phase reconstruction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.stats import linregress
from check_optical_xlsx_ingest import sheets


def row(data, index):
    values=[(j,v) for j,v in data[index].items() if j>=1]
    values.sort()
    assert values and all(j==k for k,(j,v) in enumerate(values,1))
    assert all(type(v)==float and np.isfinite(v) for j,v in values)
    return np.array([v for j,v in values])


def replay(path):
    data=sheets(path)['Fig 2e']
    assert data[1][0]=='Slit separation (fs)'
    assert data[2][0]=='Spectral oscillation period (THz)'
    x,y=row(data,1),row(data,2)
    xm,ym=row(data,3),row(data,4)
    xf,yf=row(data,5),row(data,6)
    assert len(x)==len(y)==17 and np.all(x!=0) and np.all(y>0)
    def interp(xs,ys):
        order=np.argsort(xs)
        assert len(xs)==len(np.unique(xs)) and xs.min()<=x.min() and xs.max()>=x.max()
        return np.interp(x,xs[order],ys[order])
    ideal=1000/abs(x)
    rms=lambda pred: float(np.sqrt(np.mean((y-pred)**2)))
    slope=linregress(np.log(abs(x)),np.log(y))
    t=sp.symbols('t',positive=True)
    assert sp.simplify(1000/t*t-1000)==0
    report={'article_doi':'10.1038/s41567-023-01993-w',
        'source_sha256':hashlib.sha256(Path(path).read_bytes()).hexdigest(),
        'sheet':'Fig 2e','measured_points':len(x),'separation_unit':'fs',
        'fringe_period_unit':'THz','ideal_rmse_thz':rms(ideal),
        'published_model_interpolated_rmse_thz':rms(interp(xm,ym)),
        'published_fit_interpolated_rmse_thz':rms(interp(xf,yf)),
        'median_ideal_relative_error':float(np.median(abs(y-ideal)/y)),
        'log_log_exponent':float(slope.slope),
        'log_log_exponent_stderr':float(slope.stderr),
        'no_refit':True,'no_complex_field_inference':True,
        'uncertainty_weighted':False}
    assert abs(report['log_log_exponent']+1)<.1
    return report


if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('xlsx');parser.add_argument('--receipt');args=parser.parse_args()
    result=replay(args.xlsx)
    text=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:Path(args.receipt).write_text(text)
    print(text)
    print('PASS: original measured Fig 2e, ideal law, published model/fit comparison')
