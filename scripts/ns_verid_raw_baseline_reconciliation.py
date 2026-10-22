#!/usr/bin/env python3
"""Reconcile a real matched NS baseline JSON with the canonical B7 live residual."""
import argparse
import hashlib
import json
from pathlib import Path

def digest(x):
    return hashlib.sha256(json.dumps(x,sort_keys=True,separators=(",",":")).encode()).hexdigest()

def reconcile(raw):
    if raw.get("schema_version") != "1.4.0":
        raise ValueError("unexpected schema")
    authority=raw.get("authority",{})
    if any(authority.get(k) for k in ("theorem_authority","clay_authority","promoted")):
        raise ValueError("unexpected numerical promotion")
    required=("trajectory_manifest","heldout_validation","depletion_currency_comparison",
              "bounded_turnover_potential","compact_gamma_potential")
    if any(k not in raw for k in required):
        raise ValueError("incomplete matched experiment receipt")
    cutoffs=raw["trajectory_manifest"].get("matched_cutoffs",[])
    if not set((32,48,64)).issubset(set(cutoffs)):
        raise ValueError("missing matched cutoffs")
    if "matched-N64" not in raw.get("holdout_trajectories",[]):
        raise ValueError("missing held-out trajectory")
    verdicts={
        "original_depletion":raw["heldout_validation"].get("any_nonvacuous_parameter_set_survives_holdout"),
        "replacement_currencies":raw["depletion_currency_comparison"].get("heldout_validation",{}).get("any_candidate_currency_passes_sampled_heldout_gate"),
        "signed_escape":raw["bounded_turnover_potential"].get("heldout_signed_escape_validation",{}).get("any_signed_escape_currency_passes_heldout"),
        "compact_gamma":raw["compact_gamma_potential"].get("heldout_compact_escape_validation",{}).get("any_compact_escape_currency_passes_heldout"),
    }
    if any(type(v) is not bool for v in verdicts.values()):
        raise ValueError("incomplete heldout verdicts; abstain")
    result={
        "schema":"dashi.verid.ns_abcd_bidi_raw_replay.v1",
        "source_hash":digest(raw),
        "canonical_leaf":"b7IntegratedControl",
        "matched_cutoffs":cutoffs,
        "observed_verdicts":verdicts,
        "completed_probes":["self_advection","cross_shell_currency","vorticity_turnover","projector_turnover","middle_eigenvalue","bounded_escape","compact_gamma"],
        "selected_next_move":"analytic B7 Q4/E or Q5 assumption audit, not redundant numerical probe",
        "next_probe_execution_required":False,
        "authority":{"finite_numeric_receipt":True,"analytic_B7":False,"continuum":False,"clay":False},
    }
    result["digest"]=digest(result)
    return result

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--baseline-json",type=Path,required=True)
    p.add_argument("--output-json",type=Path,required=True)
    args=p.parse_args()
    report=reconcile(json.loads(args.baseline_json.read_text()))
    args.output_json.parent.mkdir(parents=True,exist_ok=True)
    args.output_json.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print(report["digest"])

if __name__=="__main__":
    main()
