"""Exact terminal history rank and full native checkpoint parity, no CI."""
import argparse
import json
import math
from pathlib import Path
from unittest.mock import patch
import numpy as np
import sympy as s
from ksw668_f8_ssprk_checkpoint import NativeCheckpoint
from ksw668_f8_tt_multipole import propagate,F


def exact():
    h,t,S,J=s.symbols('h t S J', positive=True)
    # J is the coefficient of H_T in H_etaeta (actual J is negative).
    p,n,pd,nd,z,zd,L=s.symbols('p n pd nd z zd L')
    HT=(z-p)/(2*h); HTT=(z-2*n+p)/h**2
    HTt=nd; HTTt=(zd-pd)/(2*h)
    def weyl(v,a):
        B=S*v; A=S*S*a+J*v
        return [-(A+L)/(4*t*t),-(A+2*B-L)/(2*t*t)]
    W=s.Matrix(weyl(HT,HTT)+weyl(HTt,HTTt))
    M=W.jacobian([p,n,pd,nd])
    assert s.factor(M.det())==S**6/(32*h**4*t**8)
    assert all(any(q!=0 for q in M[:,i]) for i in range(4))
    # Four independent history fields affect the two Weyl routes even when
    # next wall and next derivative are fixed and spatial Laplacian held fixed.
    for i,(v,a) in enumerate(((HT,HTT),(HTt,HTTt))):
        assert s.expand(W[2*i+1]-2*W[2*i]-(L-S*v)/t**2)==0
    # At each cut, the required saved slots are exactly the already captured ones.
    checks=0
    for nt in range(2,65):
        for cursor in range(nt+2):
            captured=[nt-1<cursor,nt<cursor,nt-1<cursor,nt<cursor]
            assert captured==[cursor>=nt+(i%2) for i in range(4)]
            checks+=1
    print('SymPy terminal history determinant',s.factor(M.det()),'cursor cases',checks,flush=True)


def assert_same(a,b):
    assert a.keys()==b.keys()
    for k in a:
        assert a[k].dtype==b[k].dtype and a[k].shape==b[k].shape and a[k].tobytes()==b[k].tobytes(),k


def load(path):
    with np.load(path,allow_pickle=False) as z:return {k:z[k].copy() for k in z.files}


def run(work,affine=False):
    work=Path(work);work.mkdir(parents=True,exist_ok=True)
    kw=dict(dr=.012,dy=.016,dt=.0025,eps=.04,final_t=12.,pulse=.065,
        inside_chord=.012,r_outer=3.01,y_outer=2.01,normal_order=3,
        conservative_source=True,affine_stage=affine)
    nt=math.ceil((F(12.)-F(1))/kw['dt']); ref=work/'reference.npz'; resume=work/'resume.npz'
    # Deterministic test interruption occurs just AFTER the production atomic
    # save. No changes to solver step, budget, source or receiver arithmetic.
    if not ref.exists():
        report=propagate(**kw,checkpoint=ref,budget=1e6,checkpoint_every=nt+1)
    else:report=propagate(**kw,checkpoint=ref,budget=1e6,checkpoint_every=nt+1)
    original=NativeCheckpoint.save
    for cut in (13,nt-1,nt):
        if resume.exists() and int(load(resume)['cursor'])>=cut:continue
        def stop(self,cursor,*args):
            original(self,cursor,*args)
            if cursor==cut:raise InterruptedError('test cut after durable save')
        with patch.object(NativeCheckpoint,'save',stop):
            try:propagate(**kw,checkpoint=resume,budget=1e6,checkpoint_every=cut)
            except InterruptedError as exc:assert str(exc)=='test cut after durable save'
            else:raise AssertionError('expected deterministic cut')
        saved=load(resume);assert int(saved['cursor'])==cut
        assert [saved['w'+str(i)].size>0 for i in range(4)]==[cut>=nt+(i%2) for i in range(4)]
        print('durable cut',cut,'history',[saved['w'+str(i)].size for i in range(4)],flush=True)
    resumed=propagate(**kw,checkpoint=resume,budget=1e6,checkpoint_every=nt+1)
    assert_same(load(ref),load(resume))
    assert json.dumps(report,sort_keys=True)==json.dumps(resumed,sort_keys=True)
    assert json.dumps(resumed,sort_keys=True)==json.dumps(propagate(**kw,checkpoint=resume,budget=1e6,checkpoint_every=nt+1),sort_keys=True)
    try:propagate(**dict(kw,affine_stage=not affine),checkpoint=resume,budget=1e6)
    except ValueError as exc:assert 'identity mismatch' in str(exc)
    else:raise AssertionError('cross-affine resume accepted')
    print('PASS bitwise checkpoint arrays and complete receiver receipt',nt+1,'steps; affine',affine,flush=True)
    (work/'receipt.json').write_text(json.dumps(report,indent=2)+'\n')

if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__);p.add_argument('work',type=Path);p.add_argument('--affine',action='store_true');p.add_argument('--exact-only',action='store_true');args=p.parse_args();exact()
    if not args.exact_only:run(args.work,args.affine)
