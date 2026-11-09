#!/usr/bin/env python3
"""Source-safe 70-determinant upCCD-support NQS and ipie CI export regression."""
import json
import tempfile
from pathlib import Path
import numpy as np
import torch
from qcafqmc_paired_nqs import PairedSpatialNQS,paired_occupations,train_paired
from qcafqmc_molecular_fcidump import sector
from qcafqmc_nqs_ipie_particle_hole import export_particle_hole

def main():
    x=paired_occupations()
    assert x.shape==(70,16)
    model=PairedSpatialNQS()
    with torch.no_grad():
        state=model(torch.as_tensor(x,dtype=torch.long))
        assert abs(float((state.abs()**2).sum())-1.)<2e-5
        broken=x.copy()
        broken[:,8:]=np.roll(broken[:,8:],1,axis=1)
        out=model(torch.as_tensor(broken,dtype=torch.long))
        assert torch.all(out==0)
    rng=np.random.default_rng(1007)
    psi=np.exp(1j*np.linspace(0,1.5,70))/np.sqrt(70)
    walkers=rng.normal(size=(20,70))+1j*rng.normal(size=(20,70))
    walkers/=np.linalg.norm(walkers,axis=1)[:,None]
    labels=.7*(walkers@np.conj(psi))
    with tempfile.TemporaryDirectory() as d:
        root=Path(d)
        data=root/"synthetic.npz"
        np.savez(data,occupations=x,walker_amplitudes=walkers,
                 overlap_labels=labels,dataset_kind="synthetic",
                 source_url="internal:paired-state-smoke")
        ckpt=root/"paired.pt"
        receipt=train_paired(data,ckpt,epochs=2,seed=13)
        assert receipt["paired_determinants"]==70
        ci,oa,ob=export_particle_hole(ckpt,8,4,4)
        assert len(ci)==70 and oa.shape==(70,4) and ob.shape==(70,4)
        assert np.isclose(np.vdot(ci,ci).real,1.)
        assert np.all(oa==ob)
        assert len(sector(8,4,4))==4900
        print(json.dumps({"scope":"synthetic seniority-zero NQS iPie export",
                          "n_paired":len(ci),
                          "n_full_sector":len(sector(8,4,4)),
                          "validation_mse":receipt["validation_mse"],
                          "parameter_count":receipt["parameter_count"],
                          "passed":True},indent=2))
if __name__=="__main__":
    main()
