#!/usr/bin/env python3
"""Construct source-labelled nickel PySCF/iPie input configs; never run implicitly.

The 41-atom XYZ records are copied from Zhao et al. §VI.9.2.
Charge and spin MUST be supplied, and are labelled as hypotheses unless an
independently verifiable electronic-state source is attached.
"""
import argparse
import json
from pathlib import Path
from qcafqmc_nickel41_integrals import GEOMETRY_DIR,read_xyz,SOURCE,geometry_receipts

def make_configs(output_dir,charge,spin,statement,provenance_kind):
    if provenance_kind not in ("independent_hypothesis","verified_original"):
        raise ValueError("invalid electronic-state provenance")
    if provenance_kind=="verified_original" and (
            not statement.startswith(("https://","doi:","arxiv:"))):
        raise ValueError("verified_original requires an explicit retrievable source locator")
    output=Path(output_dir)
    output.mkdir(parents=True,exist_ok=True)
    receipts=geometry_receipts()
    results={}
    for name in ("B","BC","C"):
        atoms=read_xyz(GEOMETRY_DIR/(name+".xyz"))
        settings={"source_url":SOURCE,
                  "source_kind":provenance_kind,
                  "electronic_state_provenance":statement,
                  "geometry_source_sha256":receipts[name]["sha256"],
                  "nickel_structure":name,
                  "atoms":[[symbol,*position] for symbol,position in atoms],
                  "basis":"sto-3g","unit":"Angstrom",
                  "charge":int(charge),"spin":int(spin),
                  "walkers":1280,"blocks":300,
                  "steps_per_block":20,"time_step":0.005,
                  "stabilize_freq":5,"pop_control_freq":5,
                  "equilibration_blocks":50,"seed":20261109,
                  "nqs_trial_used":False,
                  "original_nickel_qcafqmc_replication":False}
        target=output/(name+".ipie.json")
        target.write_text(json.dumps(settings,indent=2)+"\n")
        results[name]={"config":str(target),"source":SOURCE,
                       "state_identity":provenance_kind}
    return results

if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("--output-dir",required=True)
    p.add_argument("--charge",type=int,required=True)
    p.add_argument("--spin",type=int,required=True)
    p.add_argument("--state-evidence",required=True)
    p.add_argument("--state-kind",choices=("independent_hypothesis","verified_original"),
                   default="independent_hypothesis")
    a=p.parse_args()
    print(json.dumps(make_configs(a.output_dir,a.charge,a.spin,
          a.state_evidence,a.state_kind),indent=2))
