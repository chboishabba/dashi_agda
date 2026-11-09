#!/usr/bin/env python3
"""Source-locked 41-atom nickel geometry and PySCF (8e,8o) producer.

IonQ/Zhao et al., arXiv:2506.22408, §VI.9.2: 41-atom XYZ B, BC, C.
Provazza et al., arXiv:2611.08129v1: STO-3G, (8e,8o).
No charge, spin or active orbital indices are silently invented.
Uses CASCI's exact inactive-core contraction for the selected MO frame,
not an unjustified slice of AO hcore or electron-repulsion integrals.
"""
import argparse
from collections import Counter
import hashlib
import json
from pathlib import Path

SOURCE="https://arxiv.org/html/2506.22408#S6.SS9.SSS2"
PUBLISHED_RHF_HARTREE={"B":-2737.810245,"BC":-2737.686838,"C":-2737.822695}
ATOMS={"Ni":28,"P":15,"O":8,"C":6,"H":1}
ROOT=Path(__file__).resolve().parents[1]
GEOMETRY_DIR=ROOT/"data/nickel_ionq_2025_reduced41"
# Pinned Git blob identities of the 41-line XYZ transcriptions from §VI.9.2.
EXPECTED_XYZ_GIT_BLOBS={
    "B":"8e3e562a9565c5814c9719a5fc1dba285a702e9e",
    "BC":"6556a19b11b65aa7ee563851158be8a4cc924842",
    "C":"a468c9eefba59c7211ed702ec5d7808678ba2cfd"}

def checked_source_bytes(path):
    path=Path(path).resolve()
    raw=path.read_bytes()
    if path.parent==GEOMETRY_DIR.resolve() and path.stem in EXPECTED_XYZ_GIT_BLOBS:
        digest=hashlib.sha1(b"blob "+str(len(raw)).encode()+bytes([0])+raw).hexdigest()
        if digest!=EXPECTED_XYZ_GIT_BLOBS[path.stem]:
            raise ValueError("source-coordinate XYZ blob differs from pinned transcription")
    return raw

def read_xyz(path):
    path=Path(path).resolve()
    lines=checked_source_bytes(path).decode("utf-8").splitlines()
    if len(lines)<2:raise ValueError("truncated XYZ file")
    count=int(lines[0])
    coordinates=[]
    for line in lines[2:]:
        fields=line.split()
        if not fields:continue
        if len(fields)!=4 or fields[0] not in ATOMS:
            raise ValueError("malformed/unknown atom in XYZ")
        symbol=fields[0];position=tuple(float(v) for v in fields[1:])
        if not all(__import__("math").isfinite(v) for v in position):
            raise ValueError("nonfinite XYZ coordinate")
        coordinates.append((symbol,position))
    if count!=41 or len(coordinates)!=count:
        raise ValueError(f"expected 41 source atoms; found {len(coordinates)}")
    return coordinates

def geometry_receipts():
    result={}
    for name in ("B","BC","C"):
        path=GEOMETRY_DIR/(name+".xyz")
        atoms=read_xyz(path)
        element_counts=dict(Counter(x[0] for x in atoms))
        nuclear_charge=sum(ATOMS[x[0]] for x in atoms)
        result[name]={"source":SOURCE,"path":str(path),
                      "sha256":hashlib.sha256(path.read_bytes()).hexdigest(),
                      "atoms":len(atoms),"element_counts":element_counts,
                      "sum_nuclear_charge":nuclear_charge,
                      "charge_and_spin_source_verified":False}
    if len({tuple(sorted(v["element_counts"].items()))
            for v in result.values()})!=1:
        raise ValueError("reaction geometries differ in elemental composition")
    return result

def produce(config_path):
    import numpy as np
    from pyscf import gto,scf,mcscf,ao2mo,tools
    config_path=Path(config_path).resolve()
    config=json.loads(config_path.read_text())
    required=("geometry","charge","spin","active_orbitals_zero_based",
              "electronic_state_source","orbital_selection_source","basis")
    missing=[key for key in required if key not in config]
    if missing:raise ValueError("missing explicit physical inputs: "+str(missing))
    if config["basis"].lower()!="sto-3g":
        raise ValueError("IonQ target nickel basis is STO-3G")
    label=config["geometry"]
    if label not in ("B","BC","C"):raise ValueError("unknown 41-atom geometry")
    if not config["electronic_state_source"] or not config["orbital_selection_source"]:
        raise ValueError("charge/spin and active space require source justification")
    indices=config["active_orbitals_zero_based"]
    if (len(indices)!=8 or len(set(indices))!=8
            or any(not isinstance(i,int) or isinstance(i,bool) or i<0
                   for i in indices)):
        raise ValueError("eight distinct nonnegative zero-based orbital indices required")
    atoms=read_xyz(GEOMETRY_DIR/(label+".xyz"))
    mol=gto.M(atom=atoms,basis="sto-3g",charge=int(config["charge"]),
              spin=int(config["spin"]),unit="Angstrom",verbose=0)
    if mol.spin!=0:raise ValueError("RHF active-space producer requires spin=0")
    mf=scf.RHF(mol)
    mf.conv_tol=float(config.get("scf_tolerance",1e-9))
    energy=mf.kernel()
    if not mf.converged:raise RuntimeError("nickel RHF failed to converge")
    from qcafqmc_molecular_scf_certificate import from_pyscf_restricted
    rhf_certificate=from_pyscf_restricted(mol,mf,tolerance=float(config.get("RHF_residual_tolerance",1e-5)))
    source_delta=float(energy-PUBLISHED_RHF_HARTREE[label])
    if abs(source_delta)>float(config.get("max_RHF_source_discrepancy_hartree",0.05)):
        raise ValueError(f"RHF energy {energy:.8f} disagrees with original Table 2 {PUBLISHED_RHF_HARTREE[label]:.8f}; verify physical state/basis/orbitals")
    if max(indices)>=mf.mo_coeff.shape[1]:
        raise ValueError("active orbital index exceeds MO count")
    ncore=(mol.nelectron-8)//2
    if (mol.nelectron-8)<0 or (mol.nelectron-8)%2 or ncore<0:
        raise ValueError("cannot place 8 active electrons in closed-shell core")
    mc=mcscf.CASCI(mf,8,8)
    # PySCF sort_mo convention is one-based; record our indices as zero-based.
    sorted_coeff=mcscf.sort_mo(mc,[i+1 for i in indices],base=1)
    h1,effective_core=mc.get_h1eff(sorted_coeff)
    eri=ao2mo.restore(1,mc.get_h2eff(sorted_coeff),8)
    if not (np.all(np.isfinite(h1)) and np.all(np.isfinite(eri))):
        raise ValueError("nonfinite molecular integrals")
    if not np.allclose(h1,h1.T,atol=1e-8):
        raise ValueError("non-symmetric core-contracted one-electron tensor")
    out_dir=Path(config.get("output_dir",config_path.parent/"nickel_integrals")).resolve()
    out_dir.mkdir(parents=True,exist_ok=True)
    # The selected MO basis is part of the physical input, not only its index list.
    # Preserve the exact sorted coefficient matrix for independently checked
    # shadow/walker/FCIDUMP frame identity.
    selected_mo=out_dir/(label+".selected_mo.npy")
    np.save(selected_mo,np.asarray(sorted_coeff,dtype="<f8"))
    selected_mo_sha256=hashlib.sha256(selected_mo.read_bytes()).hexdigest()
    fcidump=out_dir/(label+".FCIDUMP")
    tools.fcidump.from_integrals(str(fcidump),h1,eri,8,8,nuc=effective_core,ms=0)
    receipt={"scope":"41-atom nickel source-geometry, RHF/STO-3G active (8e,8o)",
             "structure":label,"geometry_url":SOURCE,
             "geometry_sha256":hashlib.sha256((GEOMETRY_DIR/(label+".xyz")).read_bytes()).hexdigest(),
             "configuration_sha256":hashlib.sha256(config_path.read_bytes()).hexdigest(),
             "charge":mol.charge,"spin":mol.spin,
             "charge_spin_source":config["electronic_state_source"],
             "orbital_selection_source":config["orbital_selection_source"],
             "active_orbital_indices_zero_based":indices,
             "selected_mo_file":str(selected_mo),
             "selected_mo_sha256":selected_mo_sha256,
             "ncore":ncore,"scf_energy_hartree":float(energy),
             "molecular_scf_certificate":rhf_certificate,
             "source_RHF_energy_hartree":PUBLISHED_RHF_HARTREE[label],
             "RHF_minus_source_hartree":source_delta,
             "nuclear_repulsion_hartree":float(mol.energy_nuc()),
             "inactive_core_plus_nuclear_hartree":float(effective_core),
             "integral_fcidump":str(fcidump),
             "integral_sha256":hashlib.sha256(fcidump.read_bytes()).hexdigest(),
             "original_ionq_orbital_frame_verified":False,
             "quantum_hardware_snapshot_source":None,
             "note":"CASCI effective core + active h1/eri; not full-space VCE AFQMC"}
    (out_dir/(label+".receipt.json")).write_text(json.dumps(receipt,indent=2)+"\n")
    return receipt

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--config")
    args=parser.parse_args()
    print(json.dumps(produce(args.config) if args.config else geometry_receipts(),indent=2))

if __name__=="__main__":
    main()
