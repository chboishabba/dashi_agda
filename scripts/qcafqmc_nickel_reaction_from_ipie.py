#!/usr/bin/env python3
"""Matched nickel AFQMC barrier/reaction analysis with conservative seed SEM.

Accepts one or more independent runs per structure; each run is a JSON
receipt produced by qcafqmc_nickel41_ipie_from_fcidump.py or
qcafqmc_nickel41_full_space_vce.py, with a real ipie energy-estimator HDF5
and original geometry SHA. Never substitutes published values for a run.

Only independent seed means are used to infer SEM, avoiding the common error
of treating 250 correlated 0.1-Eh^-1 blocks as independent.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np

KCAL_MOL_PER_HARTREE=627.5094740631
LABELS=("B","BC","C")

def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()

def select_production_blocks(raw,expected_blocks,discard):
    """Strip ipie's initial estimator before discarding production burn-in.

    ipie AFQMC.setup_estimators() writes print_block(..., 0, ...) before
    propagation; a 300-block run generally has 301 estimator rows.
    Accept 300-row exports where block zero is already absent, but require
    the exact production block count from the source receipt. Any other
    shape fails rather than silently shifting the energy time window.
    """
    arr=np.asarray(raw)
    if arr.ndim!=1:
        raise ValueError("expected one-dimensional energy estimator")
    if type(expected_blocks)!=int or expected_blocks<1:
        raise ValueError("missing valid production block count")
    if type(discard)!=int or not 0<=discard<expected_blocks:
        raise ValueError("invalid discard count")
    if len(arr)==expected_blocks+1:
        arr=arr[1:]
        dropped_block_zero=True
    elif len(arr)==expected_blocks:
        dropped_block_zero=False
    else:
        raise ValueError(
            f"energy estimator has {len(arr)} rows; expected {expected_blocks} "
            f"or {expected_blocks+1} (with block-zero estimator)")
    return arr[discard:],dropped_block_zero


def load_seed(receipt_path,discard=50,autocorrelation=True):
    receipt_path=Path(receipt_path).resolve()
    receipt=json.loads(receipt_path.read_text())
    label=receipt.get("structure")
    if label not in LABELS:raise ValueError("unrecognized nickel structure")
    file=receipt.get("estimates_hdf5") or receipt.get("estimator")
    if not file or not Path(file).is_file():
        raise ValueError("missing executed AFQMC HDF5 estimator for "+label)
    if receipt.get("executed",True) is False:
        raise ValueError("dry-run is not a measurement")
    from ipie.analysis.extraction import extract_observable
    table=extract_observable(str(file),"energy")
    if "ETotal" not in table.columns:
        raise ValueError("ipie energy estimator does not contain ETotal")
    values=np.asarray(table["ETotal"].to_numpy(),dtype=complex)
    if not np.isfinite(values).all() or np.max(abs(values.imag))>1e-4:
        raise ValueError("non-finite or unexpectedly complex energy estimates")
    expected=receipt.get("measurement_blocks",receipt.get("blocks"))
    retained,block_zero_dropped=select_production_blocks(
        values,int(expected) if expected is not None else None,discard)
    retained=retained.real
    if len(retained)<64:
        raise ValueError("too few actual production blocks for blocking diagnostic")
    blocked=None
    if autocorrelation:
        from qcafqmc_autocorrelation_reblocking import blocking_estimate
        blocked=blocking_estimate(retained)
    return {
      "label":label,
      "seed":receipt.get("seed"),
      "energy_mean_hartree":float(retained.mean()),
      "n_retained_blocks":len(retained),
      "block_zero_estimator_removed":block_zero_dropped,
      "production_blocks":int(expected),
      "blocked_within_seed_SE_hartree":blocked["standard_error"] if blocked else None,
      "blocking_tau_diagnostic":blocked["tau_int_lower_estimate"] if blocked else None,
      "geometry_sha256":receipt["geometry_sha256"],
      "trial_type":receipt.get("trial_type"),
      "hamiltonian_source_sha256":
          receipt.get("integral_sha256") or receipt.get("input_configuration_sha256"),
      "estimator_sha256":sha(file),
      "receipt_sha256":sha(receipt_path)
    }

def combine(receipt_files,discard=50,autocorrelation=True):
    records=[load_seed(x,discard,autocorrelation) for x in receipt_files]
    grouped={x:[r for r in records if r["label"]==x] for x in LABELS}
    for label,rs in grouped.items():
        if len(rs)<3:
            raise ValueError(label+": need >=3 independent seed trajectories for uncertainty diagnostic")
        ids=[r["seed"] for r in rs]
        if any(x is None for x in ids) or len(set(ids))!=len(ids):
            raise ValueError(label+": duplicate or unreported random seeds")
        if len({r["geometry_sha256"] for r in rs})!=1:
            raise ValueError(label+": inconsistent source geometry")
        if len({r["hamiltonian_source_sha256"] for r in rs})!=1:
            raise ValueError(label+": two trials or orbital frames were mixed")
        if len({r["trial_type"] for r in rs})!=1:
            raise ValueError(label+": trial types mixed in a single summary")
        if len({r["n_retained_blocks"] for r in rs})!=1:
            raise ValueError(label+": inconsistent analysis windows")
    trials={x:grouped[x][0]["trial_type"] for x in LABELS}
    if len(set(trials.values()))!=1:
        raise ValueError("B/BC/C trials must use the same trial protocol")
    moments={}
    for label,rs in grouped.items():
        numbers=np.array([r["energy_mean_hartree"] for r in rs])
        seed_se=float(np.std(numbers,ddof=1)/np.sqrt(len(numbers)))
        blocked_se=(float(np.sqrt(np.mean([r["blocked_within_seed_SE_hartree"]**2
                               for r in rs])/len(rs))) if autocorrelation else 0.)
        moments[label]={
          "mean_hartree":float(np.mean(numbers)),
          "standard_error_hartree":max(seed_se,blocked_se),
          "independent_seed_SE_hartree":seed_se,
          "within_seed_blocking_SE_hartree":blocked_se,
          "n_independent_seeds":len(numbers),
          "geometry_sha256":rs[0]["geometry_sha256"],
          "hamiltonian_source_sha256":rs[0]["hamiltonian_source_sha256"]
        }
    def contrast(label):
        # Separate-geometry independent-seed uncertainty propagation.
        d=(moments[label]["mean_hartree"]-moments["B"]["mean_hartree"])
        error=np.hypot(moments[label]["standard_error_hartree"],
                       moments["B"]["standard_error_hartree"])
        return {"delta_hartree":float(d),"SE_hartree":float(error),
                "delta_kcal_per_mol":float(d*KCAL_MOL_PER_HARTREE),
                "SE_kcal_per_mol":float(error*KCAL_MOL_PER_HARTREE)}
    return {
      "scope":"independent AFQMC seed means with optional dyadic autocorrelation blocking",
      "trial_type":next(iter(trials.values())),
      "first_n_measured_blocks_discarded":discard,
      "per_geometry":moments,
      "activation_barrier":contrast("BC"),
      "reaction_energy":contrast("C"),
      "statistical_caveat":"uncertainty diagnostic, not a validated confidence interval; blocking plateau and systematic biases unverified",
      "original_IonQ_energy_values_substituted":False,
      "records":records
    }
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("receipts",nargs="+")
    p.add_argument("--discard",type=int,default=50)
    p.add_argument("--no-autocorr",action="store_true",
                   help="diagnostic-only: suppress within-seed blocking analysis")
    a=p.parse_args()
    print(json.dumps(combine(a.receipts,a.discard,not a.no_autocorr),indent=2))
