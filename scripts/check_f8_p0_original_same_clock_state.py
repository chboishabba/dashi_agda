"""F8 P0 D1/D4 same-state native mode3 receiver-time forensic consumer.

Takes an ORIGINAL source-hash-pinned A0/A1/C0/C1 full producer JSON,
the ORIGINAL terminal NativeCheckpoint NPZ and a separate opt-in
INSTRUMENTED receiver-state sidecar made by
run_f8_p0_native_receiver_state_capture.py.

Original terminal checkpoint full U/P/M live ONE SSPRK3 lookahead step
beyond the receiver wall history; they cannot be identified as t=12.
This fails closed unless the sidecar provides exactly simultaneous
receiver-clock U/P/M and U_T and passes independent checks against
checkpoint historical w1/w3, source checksums and full receiver JSON.
No CI, no original mode4 forward, no physical continuum acceptance.
"""
import argparse,hashlib,json,math
from pathlib import Path
import numpy as np

ELL=(0,2,4)
def sha(x):return hashlib.sha256(x.tobytes()).hexdigest()
def cubic(r,dr,nr):
    ir=int(math.floor(r/dr));q=r/dr-ir
    indices=np.arange(ir-1,ir+3)
    if indices[0]<0 or indices[-1]>=nr-1:raise ValueError('out-of-interior original cubic stencil')
    weights=np.array([-q*(q-1)*(q-2)/6,(q+1)*(q-1)*(q-2)/2,
                      -(q+1)*q*(q-2)/2,(q+1)*q*(q-1)/6])
    return indices,weights

def diagnose(U,P,M,Ut,source,dr,dy,b,v,amp):
    if U.ndim!=3 or U.shape!=P.shape or U.shape!=M.shape or U.shape!=Ut.shape:
        raise ValueError('nonidentical original 3D stage arrays')
    nm,ny,nr=U.shape
    if nm!=3 or ny<3 or nr<5 or source.shape!=(3,nr):
        raise ValueError('original dimension/source mismatch')
    if not all(np.isfinite(x).all() for x in (U,P,M,Ut,source)):
        raise ValueError('nonfinite original state')
    # Mode3 has Dirichlet radial endpoint: stage(U) sets U_T=0 there.
    W=((1+v)*P+(1-v)*M)/2
    assert np.allclose(Ut[:,:,:-1],W[:,:,:-1],rtol=1e-12,atol=2e-13)
    Q=np.empty_like(U)
    Q[:,0,:]=(P[:,0,:]-M[:,0,:])/2-(U[:,1,:]-U[:,0,:])/dy
    Q[:,-1,:]=(P[:,-1,:]-M[:,-1,:])/2-(U[:,-1,:]-U[:,-2,:])/dy
    Q[:,1:-1,:]=(P[:,1:-1,:]-M[:,1:-1,:])/2-(U[:,2:,:]-U[:,:-2,:])/(2*dy)
    G=((1+v)*P[:,0,:]+(v-1)*M[:,0,:])/2
    source_boundary=amp*source
    V=np.stack([(((np.arange(nr)+.5)*dr)**d-
                  ((np.maximum(np.arange(nr)-.5,0))*dr)**d)/d for d in (3,7,11)])
    def weighted(x):
        return float(np.sqrt(np.sum(V*x*x)))
    return dict(Q_wall_weighted_l2=weighted(Q[:,0,:]),
                Q_upper_weighted_l2=weighted(Q[:,-1,:]),
                Q_full_max_abs=float(np.max(np.abs(Q[:,:,:-1]))),
                israel_residual_weighted_l2=weighted(G-source_boundary),
                israel_residual_max_abs=float(np.max(np.abs(G-source_boundary))),
                upper_incoming_P_weighted_l2=weighted(P[:,-1,:]),
                pre_weyl_wall_U_weighted_l2=weighted(U[:,0,:]),
                source_wall_weighted_l2=weighted(source_boundary),
                complete_receiver_state_kinematic_Q_equals_zero=False,
                original_stage_ut_max_error=float(np.max(np.abs(Ut[:,:,:-1]-W[:,:,:-1]))))

def read(ckpath,sidepath,prodpath):
    receipt=json.loads(Path(prodpath).read_text())
    with np.load(ckpath,allow_pickle=False) as z:
        identity_string=z['identity'].item()
        identity=json.loads(identity_string)
        cursor=int(z['cursor'].item())
        walls=[z['w'+str(i)].copy() for i in range(4)]
        actual_checkpoint_U=z['U'].copy()
    if cursor!=identity['config']['nt']+1 or cursor!=receipt['steps']+1:
        raise ValueError('not completed original producer checkpoint')
    if len(walls)!=4 or any(w.shape!=(3,receipt['radius_bins']) for w in walls):
        raise ValueError('missing original four wall histories')
    with np.load(sidepath,allow_pickle=False) as z:
        meta=json.loads(z['metadata'].item())
        U,P,M,Ut,source=[z[k].copy() for k in ('U','P','M','Ut','source')]
        dr,dy,b,v,amp=[float(z[k].item()) for k in ('dr','dy','b','v','amp')]
    expected_label=Path(prodpath).stem
    if meta['label']!=expected_label:raise ValueError('source/receiver label mismatch')
    expected_meta=hashlib.sha256(identity_string.encode()).hexdigest()
    if meta['original_checkpoint_identity_sha256']!=expected_meta:
        raise ValueError('stale sidecar checkpoint identity')
    if meta['original_checkpoint_wall_sha256']!=sha(walls[1]):
        raise ValueError('stale sidecar wall')
    if meta['original_solver_sha256']!=identity['source']['ksw668_f8_tt_multipole.py']:
        raise ValueError('original solver source mismatched')
    if sha(source)!=identity['arrays'][0]:
        raise ValueError('source cell loads do not match NativeCheckpoint source')
    if U.shape!=actual_checkpoint_U.shape or not np.array_equal(U[:,0,:],walls[1]):
        raise ValueError('instrumented receiver state mismatches original stored t12 wall')
    if not np.array_equal(Ut[:,0,:],walls[3]):
        raise ValueError('instrumented same-time tangent mismatches original t12 wall')
    for key,expected in (('dr',receipt['step_radial']),('dy',receipt['step_bulk']),
                         ('b',1/receipt['receiver_t'])):
        if not math.isclose(locals()[key],expected,rel_tol=0,abs_tol=1e-12):
            raise ValueError('wrong physical geometry/grid time')
    if receipt['normal_order']!=3 or identity['config']['normal_order']!=3:
        raise ValueError('this consumer supports ONLY original native mode3')
    assert identity['config']['conservative_source']
    if not math.isclose(v,-1/math.sqrt(1+receipt['receiver_t']**2),abs_tol=1e-12):
        raise ValueError('moving brane velocity mismatch')
    diag=diagnose(U,P,M,Ut,source,dr,dy,b,v,amp)
    outputs={}
    for place,r,key in (('near',receipt['nominal_receiver_r'],'raw_mode_values'),
                        ('far',receipt['far_receiver_grid_r'],'far_mode_values')):
        ids,w=cubic(r,dr,U.shape[2])
        H=np.array([(r/receipt['eps'])**ell*(w@U[i,0,ids]) for i,ell in enumerate(ELL)])
        expected=np.asarray(receipt[key])
        if not np.allclose(H,expected,rtol=1e-10,atol=1e-15):
            raise ValueError('original signed full receipt field mismatch: '+place)
        Qr=np.array([(r/receipt['eps'])**ell*(w@
               ((P[i,0,ids]-M[i,0,ids])/2-(U[i,1,ids]-U[i,0,ids])/dy))
               for i,ell in enumerate(ELL)])
        Gr=np.array([(r/receipt['eps'])**ell*(w@
               ((1+v)*P[i,0,ids]+(v-1)*M[i,0,ids])/2)
               for i,ell in enumerate(ELL)])
        outputs[place]=dict(r=r,original_stencil=ids.tolist(),mode_H=H.tolist(),
                            mode_Q_wall=Qr.tolist(),mode_G_wall=Gr.tolist(),
                            signed_H=float(np.sum(H)),
                            signed_Q_wall=float(np.sum(Qr)),
                            signed_G_wall=float(np.sum(Gr)))
    return dict(status='PASS source-pinned simultaneous original t12 receiver state; physical convergence OPEN',
                source_label=expected_label,source_sha256=identity['source'],
                receiver_time=receipt['receiver_t'],cursor=cursor,
                checkpoint_full_U_time='t12+dt lookahead; not mixed with receiver data',
                capture_U_P_M_Ut_time='t12 before lookahead',
                state_diagnostics=diag,receivers=outputs,
                native_mode4_forward='NOT_PRESENT in original propagate; separate semidiscrete owner',
                original_continuum_far_causal_null='FAIL finite, still open',
                physical_theorem_accepted=False)

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--checkpoint',type=Path,required=True)
    parser.add_argument('--sidecar',type=Path,required=True)
    parser.add_argument('--production-json',type=Path,required=True)
    a=parser.parse_args()
    print(json.dumps(read(a.checkpoint,a.sidecar,a.production_json),indent=2))
