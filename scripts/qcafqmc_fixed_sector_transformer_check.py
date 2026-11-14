#!/usr/bin/env python3
"""Tiny source-labelled synthetic smoke fixture for fixed-sector 16-qubit NQS.

NEVER submit this as original matchgate observations or the nickel dataset.
"""
import itertools
import json
import tempfile
from pathlib import Path
import numpy as np
from qcafqmc_fixed_sector_transformer import read_data,train,AutoregressiveNQS
import torch

def main():
    rng=np.random.default_rng(20261109)
    configs=[]
    for a in range(8):
        for b in range(8):
            bits=np.zeros(16,dtype=np.int64);bits[a]=bits[8+b]=1
            configs.append(bits)
    x=np.array(configs)
    theta=(x@np.arange(1,17))*0.07
    psi=np.exp(1j*theta)/np.sqrt(len(x))
    walkers=rng.normal(size=(24,len(x)))+1j*rng.normal(size=(24,len(x)))
    walkers/=np.linalg.norm(walkers,axis=1)[:,None]
    labels=.72*(walkers@np.conj(psi))
    labels+=.0001*(rng.normal(size=len(labels))+1j*rng.normal(size=len(labels)))
    with tempfile.TemporaryDirectory() as temp:
        path=Path(temp)/"synthetic.npz"
        np.savez(path,occupations=x,walker_amplitudes=walkers,
                 overlap_labels=labels,n_alpha=1,n_beta=1,
                 dataset_kind="synthetic",
                 source_url="internal:qcafqmc_synthetic_transformer_check")
        d=read_data(path)
        assert len(d["occupations"])==64
        model=AutoregressiveNQS()
        assert sum(p.numel() for p in model.parameters())==12892
        with torch.no_grad():
            norm=float((model(torch.as_tensor(x),1,1).abs()**2).sum())
        assert abs(norm-1.)<1e-5
        result=train(path,Path(temp)/"model.pt",epochs=2,seed=17)
        assert result["dataset_kind"]=="synthetic"
        assert result["original_ionq_weights"] is False
        assert np.isfinite(result["best_validation_complex_overlap_mse"])
        print(json.dumps({"scope":"synthetic 16-qubit 1+1-electron NQS smoke",
                          "validation_mse":result["best_validation_complex_overlap_mse"],
                          "parameters":result["parameter_count"],
                          "passed":True},indent=2))
if __name__=="__main__":
    main()
