"""F8 integrated W1/W2 acceptance: actual full-band History, signed Ward,
controller, elastic, nonzero/zero output and constrained Schur controls.
Run locally in repo: OPENBLAS_NUM_THREADS=1 timeout 90 python scripts/check_f8_w1w2_integrated_receipt.py
Actual finite diagnostic only; source/cutoff/normal/receiver certification remains open.
"""
import numpy as np
from check_f8_full_band_ward_attachment import assemble,exact as ward_exact
from check_f8_scalar_density_momentum_schur import exact as schur_exact
from check_f8_full_band_wall_controller import History,Q
from check_f8_material_clock_controller import source_shear_bound

def run(K=20.,cells=64,nh=8,nodes=3):
    ward_exact()
    schur_exact()
    h=History(K=K,cells=cells,nh=nh,nodes=nodes,end=1.045)
    t=1.035
    assert np.max(abs(h.ctrl(1.)[0]))==0
    # Nonzero source and angle: rotate Q by a genuine SO(3) transformation.
    th=np.pi/7
    R=np.array([[np.cos(th),-np.sin(th),0],
                [np.sin(th), np.cos(th),0],[0,0,1]])
    qrot=R.T@Q@R
    assert np.allclose(np.linalg.eigvalsh(qrot),[-1,0,1])
    rows=[]
    for k in (0.,K/2,3*K/2,5*K/2,3*K,3*K+1):
        T,C,W=assemble(h,t,k,muS=0.,Qrot=qrot)
        assert np.isfinite(np.r_[T.ravel(),C.ravel(),W]).all()
        assert abs(T[0,0])+abs(C[0,0])<1e-10 if k>2*K else True
        if k>=3*K:
            assert np.max(abs(T))<1e-13 and np.max(abs(C))<1e-13
            assert np.max(abs(W))<1e-13
        rows.append((k,float(np.linalg.norm(T)),float(np.linalg.norm(C)),
                     float(np.linalg.norm(W))))
    # Keep the actual fixed-action shear coefficient explicit; S=1 is only
    # the perturbative coefficient-level normalization, not a physical unit drive.
    actual_mu=source_shear_bound()+1
    phys=assemble(h,t,K/2,muS=actual_mu,Qrot=qrot)
    assert all(np.isfinite(v).all() for v in phys)
    # Elastic is strictly a K-supported term: never extend it to 3K.
    high=assemble(h,t,5*K/2,muS=7.,Qrot=qrot)
    base=assemble(h,t,5*K/2,muS=0.,Qrot=qrot)
    assert all(np.allclose(a,b) for a,b in zip(high,base))
    # Full real-source output is real for the supplied antipodal source.
    assert max(np.max(abs(v.imag)) for v in assemble(h,t,0.,Qrot=qrot))<1e-8
    print('F8 finite-band W1/W2 rows (k,stress,Israel,Ward):',rows,flush=True)
    print('PASS algebra and finite source receipt; no derivative/cutoff physical acceptance')
    return rows

if __name__=='__main__':run()
