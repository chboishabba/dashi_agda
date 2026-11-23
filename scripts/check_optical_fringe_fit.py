"""Provenance-gated, intensity-only temporal fringe fit on selected XLSX columns.

This regression NEVER reclassifies a manifest as authenticated experimental data.
The test workbook is synthetic, and recovered delay is in inverse-frequency units.
"""
import hashlib
import json
import tempfile
from pathlib import Path
import numpy as np
import sympy as sp
from scipy.optimize import minimize_scalar
from openpyxl import Workbook
from check_optical_xlsx_ingest import ingest


def fit_fringe(x, y, delay_bounds=(0.2, 4.0), grid_points=250):
    x=np.asarray(x,dtype=float); y=np.asarray(y,dtype=float)
    assert x.ndim==y.ndim==1 and x.size==y.size and x.size>=40
    assert np.all(np.isfinite(x)) and np.all(np.isfinite(y)) and np.all(y>=0)
    assert np.all(np.diff(x)>0) and delay_bounds[0]>0 and delay_bounds[1]>delay_bounds[0]
    # A slowly varying quadratic background prevents mistaking curvature for fringes.
    u=(x-x.mean())/(x.max()-x.min())
    bg=np.column_stack([np.ones(len(x)),u,u*u])
    # Deterministic alternate-bin holdout; no data leakage in coefficient solve.
    train=np.arange(len(x))%2==0; test=~train
    def coeff(tau, fitmask):
        theta=2*np.pi*tau*(x-x.mean())
        design=np.column_stack([bg,np.cos(theta),np.sin(theta)])
        c=np.linalg.lstsq(design[fitmask],y[fitmask],rcond=None)[0]
        return c,design
    def training_mse(tau):
        c,d=coeff(tau,train)
        return float(np.mean((y[train]-d[train]@c)**2))
    grid=np.linspace(*delay_bounds,grid_points)
    errors=np.array([training_mse(t) for t in grid])
    minima=np.argsort(errors)[:min(8,len(grid))]
    candidates=[]
    for i in minima:
        low=grid[max(0,i-1)];high=grid[min(len(grid)-1,i+1)]
        r=minimize_scalar(training_mse,bounds=(low,high),method='bounded',options={'xatol':1e-12})
        candidates.append((r.fun,float(r.x)))
    _,tau=min(candidates)
    c,d=coeff(tau,train)
    bgc=np.linalg.lstsq(bg[train],y[train],rcond=None)[0]
    mse_model=float(np.mean((y[test]-d[test]@c)**2))
    mse_background=float(np.mean((y[test]-bg[test]@bgc)**2))
    return {'delay_inverse_frequency':tau,'phase_rad':float(np.arctan2(-c[4],c[3])),
            'amplitude':float(np.hypot(c[3],c[4])),
            'holdout_mse_model':mse_model,'holdout_mse_background':mse_background,
            'holdout_improvement':mse_background-mse_model,'points':len(x),
            'complex_optical_field_inferred':False}


def fit_from_workbook(path,manifest_path,require_measured=True):
    provenance=ingest(path,manifest_path,require_measured=require_measured,return_pairs=True)
    result=fit_fringe(*np.asarray(provenance['pairs'],dtype=float).T)
    result.update({'source_sha256':provenance['sha256'],'trace_kind':provenance['trace_kind'],
                   'publication_authenticated':False,
                   'source_kind':provenance['source_kind'],
                   'frequency_unit':provenance['frequency_unit']})
    return result


def tests():
    t,f,phase=sp.symbols('t f phase',real=True)
    assert sp.simplify(sp.expand_trig(sp.cos(t+phase))-(sp.cos(t)*sp.cos(phase)-sp.sin(t)*sp.sin(phase)))==0
    count=1
    with tempfile.TemporaryDirectory() as td:
        f=Path(td)/'synthetic.xlsx';manifest=Path(td)/'synthetic.json'
        wb=Workbook();ws=wb.active;ws.title='Synthetic Raw';ws.append(['Frequency','Intensity'])
        xx=np.linspace(0,10,181)
        yy=.8+.12*(xx-5)/5+.24*np.cos(2*np.pi*1.35*(xx-5)+.4)+.015*np.sin(xx*.71)
        assert min(yy)>0
        for a,b in zip(xx,yy):ws.append([float(a),float(b)])
        wb.save(f)
        m={'source_kind':'synthetic','trace_kind':'raw','source_reference':'synthetic fixture - not a publication',
           'frequency_unit':'arb','intensity_unit':'arb','worksheet':'Synthetic Raw',
           'first_data_row':2,'frequency_column':1,'intensity_column':2,
           'sha256':hashlib.sha256(f.read_bytes()).hexdigest()}
        manifest.write_text(json.dumps(m))
        z=fit_from_workbook(f,manifest,False)
        assert abs(z['delay_inverse_frequency']-1.35)<.01,z;count+=1
        assert z['holdout_improvement']>.01,z;count+=1
        assert z['amplitude']>.20;count+=1
        assert z['publication_authenticated'] is False;count+=1
        try:fit_from_workbook(f,manifest,True)
        except AssertionError:count+=1
        else:raise AssertionError('synthetic source accepted as experimental')
        flat=fit_fringe(xx,.8+.12*(xx-5)/5+0*xx)
        assert flat['holdout_improvement']<1e-12;count+=1
        y2=.8+.12*(xx-5)/5+.24*np.cos(2*np.pi*1.35*(xx-5)+.8)
        z2=fit_fringe(xx,y2)
        assert abs(z2['delay_inverse_frequency']-z['delay_inverse_frequency'])<.02;count+=1
        assert abs(np.angle(np.exp(1j*(z2['phase_rad']-z['phase_rad']))))>.2;count+=1
        print('synthetic fit:',json.dumps(z,indent=2))
    print(f'{count}/{count} PASS (local SymPy + deterministic intensity fitting)')


if __name__=='__main__':tests()
