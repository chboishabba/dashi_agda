#!/usr/bin/env python3
"""End-to-end SYNTHETIC 16-qubit NQS-guided Hubbard regression.

No real nickel, no original IonQ data. Produces its own harmless synthetic
FCIDUMP and *postprocessed* overlap-label control; trains the NQS and guides
a finite phaseless auxiliary-field walk on the SAME resulting Hamiltonian.
"""
import itertools
import json
from pathlib import Path
import tempfile
import numpy as np
from qcafqmc_fixed_sector_transformer import train
from qcafqmc_nqs_guided_hubbard16 import run

def synthetic_inputs(root):
    n=8;na=nb=1
    fcidump=root/"hubbard_8orbitals.FCIDUMP"
    lines=["&FCI NORB=8, NELEC=2, MS2=0,"," ORBSYM=1,1,1,1,1,1,1,1,"," ISYM=1,","&END"]
    for i in range(3,9):
        lines.append(f" 10.0 {i} {i} 0 0")
    lines.append(" -1.0 1 2 0 0")
    for i in (1,2):
        lines.append(f" 4.0 {i} {i} {i} {i}")
    lines.append(" 0.0 0 0 0 0")
    fcidump.write_text("\n".join(lines)+"\n")
    configs=[]
    for a,b in itertools.product(range(n),repeat=2):
        bit=np.zeros(2*n,dtype=np.int64);bit[a]=bit[n+b]=1
        configs.append(bit)
    configurations=np.array(configs)
    psi=np.exp(1j*np.linspace(0,1,len(configs)))/np.sqrt(len(configs))
    rng=np.random.default_rng(911)
    walker=rng.normal(size=(28,len(configs)))+1j*rng.normal(size=(28,len(configs)))
    walker/=np.linalg.norm(walker,axis=1)[:,None]
    observations=.72*(walker@np.conj(psi))
    path=root/"synthetic_postprocessed_overlaps.npz"
    np.savez(path,occupations=configurations,walker_amplitudes=walker,
             overlap_labels=observations,n_alpha=na,n_beta=nb,
             dataset_kind="synthetic",source_url="internal:qcafqmc-end-to-end")
    return fcidump,path

def main():
    with tempfile.TemporaryDirectory() as path:
        root=Path(path)
        integrals,observations=synthetic_inputs(root)
        checkpoint=root/"synthetic_nqs.pt"
        training=train(observations,checkpoint,epochs=3,seed=5)
        result=run(integrals,checkpoint,walkers=20,steps=3,seed=5,branch_every=0)
        energies=np.array([x["mixed_energy_real"] for x in result["history"]])
        assert np.all(np.isfinite(energies))
        assert np.isclose(result["FCI_ground_energy"],2-2*np.sqrt(2),atol=1e-9)
        assert training["dataset_kind"]=="synthetic"
        print(json.dumps({"scope":"synthetic NQS-guided Hubbard end-to-end smoke",
                          "source":training["source_url"],
                          "FCI_ground":result["FCI_ground_energy"],
                          "mixed_energies":energies.tolist(),
                          "training_validation_mse":training["best_validation_complex_overlap_mse"],
                          "original_ionq_replication":False},indent=2))
if __name__=="__main__":
    main()
