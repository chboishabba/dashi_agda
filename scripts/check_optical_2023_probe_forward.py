"""OL3d: published optical switching model and held-out measured map.

Requires original MOESM3/MOESM5 workbooks; never redistributes source data.
The learnt envelope/interpolated coefficients are NOT a complete optical theory.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.interpolate import PchipInterpolator
from scipy.ndimage import gaussian_filter1d
from scipy.signal import find_peaks
from check_optical_xlsx_ingest import sheets


def workbook(path):
    return {name:{(r,c+1):v for r,values in rows.items() for c,v in values.items()}
            for name,rows in sheets(path).items()}


def numeric_row(sheet, row):
    cols=sorted(c for r,c in sheet if r==row and c>=2)
    assert cols and cols==list(range(2,cols[-1]+1))
    return np.asarray([sheet[row,c] for c in cols],dtype=float)


def analyse(source_3, source_5):
    tab=workbook(source_3)['Fig 2f']
    f=np.array([tab[1,c] for c in range(3,643)])
    delays=np.array([tab[r,1] for r in range(3,30)])
    measured=np.array([[tab[r,c] for c in range(3,643)] for r in range(3,30)])
    assert measured.shape==(27,640) and np.all(np.diff(f)<0)
    assert int((measured<0).sum())==4058
    checks=2
    slit=workbook(source_5)['Extended Fig 2a']
    t=numeric_row(slit,1); r=numeric_row(slit,2)
    peaks,_=find_peaks(r,prominence=.10,distance=80)
    assert len(peaks)==2
    peak_separation=float(abs(np.diff(t[peaks])[0]));checks+=1
    switching,_=find_peaks(np.gradient(r,t),prominence=.001,distance=80)
    assert len(switching)==2;checks+=1
    switching_separation=float(abs(np.diff(t[switching])[0]))
    assert 750<peak_separation<850 and 750<switching_separation<850;checks+=1
    omega,tau=sp.symbols('omega tau',real=True)
    F=1+sp.exp(-sp.I*omega*tau)
    assert sp.trigsimp(sp.expand_complex(F*sp.conjugate(F))-2-2*sp.cos(omega*tau))==0;checks+=1
    order=np.argsort(delays);x=delays[order];y=measured[order]
    train=np.arange(len(x))%4!=0;train[[0,-1]]=True;test=~train
    assert train.sum()==21 and test.sum()==6;checks+=1
    envelope=gaussian_filter1d(y[train].mean(axis=0),sigma=3)
    results={}
    for nh in (0,1,2):
        coeff=[]
        for i in np.where(train)[0]:
            theta=2*np.pi*(f-230.)*x[i]/1000.
            columns=[envelope]
            for h in range(1,nh+1):
                columns.extend([envelope*np.cos(h*theta),envelope*np.sin(h*theta)])
            coeff.append(np.linalg.lstsq(np.column_stack(columns),y[i],rcond=1e-8)[0])
        coeff=np.asarray(coeff)
        interpolation=PchipInterpolator(x[train],coeff,axis=0)
        pred=np.empty_like(y)
        for i in range(len(x)):
            theta=2*np.pi*(f-230.)*x[i]/1000.
            columns=[envelope]
            for h in range(1,nh+1):
                columns.extend([envelope*np.cos(h*theta),envelope*np.sin(h*theta)])
            pred[i]=np.column_stack(columns)@interpolation(x[i])
        res=pred[test]-y[test]
        results[str(nh)]={'harmonics':nh,'heldout_delay_rows_fs':x[test].tolist(),
            'heldout_rmse_mhz':float(np.sqrt(np.mean(res**2))),
            'heldout_mae_mhz':float(np.mean(abs(res))),
            'heldout_p95_abs_mhz':float(np.quantile(abs(res),.95)),
            'heldout_max_abs_mhz':float(np.max(abs(res))),
            'scalar_parameters':int(envelope.size+coeff.size),
            'template_from_training_rows':True,'heldout_rows_used_for_training':False}
        assert np.all(np.isfinite(pred)) and results[str(nh)]['heldout_rmse_mhz']>0;checks+=1
    assert results['2']['heldout_rmse_mhz']<results['0']['heldout_rmse_mhz'];checks+=1
    return {'article_doi':'10.1038/s41567-023-01993-w',
        'source_3_sha256':hashlib.sha256(Path(source_3).read_bytes()).hexdigest(),
        'source_5_sha256':hashlib.sha256(Path(source_5).read_bytes()).hexdigest(),
        'measured_map':'Fig 2f','realistic_slit_model':'Extended Fig 2a',
        'grid_shape':list(measured.shape),'negative_signed_measurements':int((measured<0).sum()),
        'realistic_slit_peak_separation_fs':peak_separation,
        'realistic_slit_rise_separation_fs':switching_separation,
        'fringe_law':'cos(2*pi*(frequency_THz-reference_THz)*delay_fs/1000)',
        'benchmark':'train-row-learned envelope, physical delay carrier, interpolated nuisance coefficients',
        'results':results,'checks':checks,'physical_table_replacement_accepted':False}


if __name__=='__main__':
    a=argparse.ArgumentParser();a.add_argument('moesm3');a.add_argument('moesm5');a.add_argument('--receipt')
    args=a.parse_args();result=analyse(args.moesm3,args.moesm5)
    data=json.dumps(result,indent=2,sort_keys=True)+'\n'
    if args.receipt:Path(args.receipt).write_text(data)
    print(data);print(f'{result["checks"]}/{result["checks"]} PASS local SymPy and measured source checks')
