"""XCIV checkpoint forensics: pre-Weyl F8 wall stencil from NativeCheckpoint.

Requires ORIGINAL existing production NPZ and full original JSON. It does
NOT run a propagator, fabricate its output or equate an old checkpoint
fingerprint to a modified solver. No CI.
"""
import argparse,json,math
from pathlib import Path
import numpy as np

ELL=(0,2,4)

def read(checkpoint,receipt):
    prod=json.loads(Path(receipt).read_text())
    assert prod['normal_order']==3 and prod['original_radial_multipoles']==[0,2,4]
    assert prod['intrinsic_4D_weyl_spatial_operator']=='full_reconstructed_Delta3'
    with np.load(checkpoint,allow_pickle=False) as z:
        assert set(('identity','cursor','U','P','M','w0','w1','w2','w3')).issubset(z.files)
        identity=json.loads(z['identity'].item())
        cursor=int(z['cursor'].item())
        U,P,M=(z[n].copy() for n in ('U','P','M'))
        wall=[z['w'+str(i)].copy() for i in range(4)]
    conf=identity['config']
    assert cursor==int(prod['steps'])+1==int(conf['nt'])+1
    assert identity['dims']==list(U.shape)
    assert U.shape==P.shape==M.shape==(3,int(prod['bulk_bins']),int(prod['radius_bins']))
    assert all(a.dtype==np.float64 and np.isfinite(a).all() for a in (U,P,M,*wall))
    assert all(w.shape==(3,U.shape[2]) for w in wall)
    assert conf['normal_order']==3 and conf['conservative_source']
    assert not conf.get('weak_source_load',False)
    for k,prodkey in [('dr','step_radial'),('dy','step_bulk'),('dt','step_time'),('eps','eps'),('final_t','receiver_t')]:
        assert math.isclose(conf[k],prod[prodkey],rel_tol=0,abs_tol=1e-14)
    assert 'source' in identity and 'ksw668_f8_tt_multipole.py' in identity['source']
    assert 'ksw668_f8_fv_source_flux.py' in identity['source']
    out={}
    for place, r, field in (('near',prod['nominal_receiver_r'],prod['raw_mode_values']),
                             ('far',prod['far_receiver_grid_r'],prod['far_mode_values'])):
        dr=prod['step_radial'];eps=prod['eps'];x=r/dr;j=math.floor(x);q=x-j
        indices=np.arange(j-1,j+3)
        assert indices[0]>=0 and indices[-1]<U.shape[2]-1
        weights=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,
             -(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
        calc=np.array([(r/eps)**ell * np.dot(weights,wall[1][m,indices]) for m,ell in enumerate(ELL)])
        expected=np.asarray(field,dtype=np.float64)
        assert np.allclose(calc,expected,rtol=1e-10,atol=1e-15),(
            place,'checkpoint field/interpolation mismatch',calc,expected)
        out[place]={
            'r':r,'stencil_indices':indices.tolist(),
            'raw_now_wall_stencil':wall[1][:,indices].tolist(),
            'raw_prev_wall_stencil':wall[0][:,indices].tolist(),
            'raw_prev_tangent_stencil':wall[2][:,indices].tolist(),
            'raw_now_tangent_stencil':wall[3][:,indices].tolist(),
            'reconstructed_H_modes':calc.tolist(),
            'receipt_H_modes':expected.tolist(),
            'max_field_reconstruction_error':float(np.max(np.abs(calc-expected))),
            'any_raw_field_nonzero_by_mode':[bool(np.any(wall[1][m,indices]!=0)) for m in range(3)]}
    assert all(out['far']['any_raw_field_nonzero_by_mode'])
    return {'status':'PASS native checkpoint/raw wall to full production field correspondence; PHYSICAL FAR NULL OPEN/FAIL',
            'checkpoint':str(checkpoint),'production_receipt':str(receipt),
            'source_sha256':identity['source'],'cursor':cursor,
            'near_far':out,'scope':'Actual terminal wall history and cubic reconstruction; does not establish continuum finite-speed, physical accuracy, or propagation cause.'}

if __name__=='__main__':
    p=argparse.ArgumentParser()
    p.add_argument('--checkpoint',required=True,type=Path)
    p.add_argument('--production-json',required=True,type=Path)
    args=p.parse_args()
    print(json.dumps(read(args.checkpoint,args.production_json),indent=2))
