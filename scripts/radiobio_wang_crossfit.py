#!/usr/bin/env python3
"""Independent post-preprocessing crossfit for Wang et al. eNeuro 2019.
Original DOI 10.1523/ENEURO.0483-18.2019; data at Caltech D1.930/D1.931.
Scientific results and original software belong to original authors.
This script accepts PRECOMPUTED baseline-adjusted per-trial alpha TF arrays;
it is NOT the original Morlet/ERP pipeline or a source EEG reproduction.
"""
import argparse
import hashlib
import json
from pathlib import Path
import numpy as np

CONDITIONS = ("active_sweep", "active_fixed", "sham_sweep", "sham_fixed")
WEIGHTS = np.array([1., -1., -1., 1.])

def validate(power, condition, subject_id, trial_id, times, freq):
    power = np.asarray(power, dtype=np.float64)
    condition = np.asarray(condition).astype(str)
    subject_id = np.asarray(subject_id).astype(str)
    trial_id = np.asarray(trial_id).astype(str)
    times, freq = np.asarray(times, dtype=float), np.asarray(freq, dtype=float)
    if power.ndim != 3 or power.shape != (len(condition), len(times), len(freq)):
        raise ValueError("power must be trials x times x frequencies")
    if len(condition) != len(subject_id) or len(condition) != len(trial_id):
        raise ValueError("IDs and condition lengths differ")
    if not (np.isfinite(power).all() and np.isfinite(times).all() and np.isfinite(freq).all()):
        raise ValueError("nonfinite measurements")
    if len(set(zip(subject_id, trial_id))) != len(trial_id):
        raise ValueError("duplicate subject/trial identifiers")
    if not (np.all(np.diff(times)>0) and np.all(np.diff(freq)>0)):
        raise ValueError("time/frequency coordinates must strictly increase")
    if not set(condition).issubset(CONDITIONS):
        raise ValueError("unknown condition labels")
    if not (np.all((times>=-2)&(times<=4)) and np.all((freq>=1)&(freq<=100))):
        raise ValueError("implausible coordinates: audit preprocessing")
    return power, condition, subject_id, trial_id, times, freq

def cell_means(power, conditions, sample_mask):
    means=[]
    for name in CONDITIONS:
        cell=power[(conditions==name)&sample_mask]
        if len(cell)==0:
            raise ValueError("unpaired subject/condition")
        means.append(cell.mean(axis=0))
    return np.stack(means)

def select_window(train, times, freq, search_freq=(6.,14.),
                  search_time=(0.,1.), width_sec=.25, width_hz=5.):
    pooled=train.mean(axis=0)
    mask=((times[:,None]>=search_time[0])&(times[:,None]<=search_time[1])
          &(freq[None,:]>=search_freq[0])&(freq[None,:]<=search_freq[1]))
    if not mask.any():
        raise ValueError("no selection cells available")
    ti,fi=np.unravel_index(np.argmin(np.where(mask,pooled,np.inf)),pooled.shape)
    wt=np.abs(times-times[ti])<=width_sec/2+1e-12
    wf=np.abs(freq-freq[fi])<=width_hz/2+1e-12
    return ti,fi,wt,wf

def run_crossfit(power,condition,subject_id,trial_id,times,freq,
                 seed=20261122,n_splits=20,min_per_cell=2):
    power,condition,subject_id,trial_id,times,freq=validate(
        power,condition,subject_id,trial_id,times,freq)
    results=[]
    for subject in sorted(set(subject_id)):
        indices=np.where(subject_id==subject)[0]
        cells=[indices[condition[indices]==name] for name in CONDITIONS]
        counts=dict(zip(CONDITIONS,map(len,cells)))
        if min(map(len,cells))<2*min_per_cell:
            results.append({"subject_id":subject,"status":"INCOMPLETE","trial_counts":counts})
            continue
        splits=[]
        for split in range(n_splits):
            digest=hashlib.sha256(f"{seed}|{subject}|{split}".encode()).digest()
            rng=np.random.default_rng(int.from_bytes(digest[:8],"big"))
            train=np.zeros(len(condition),dtype=bool)
            held=np.zeros(len(condition),dtype=bool)
            for cell in cells:
                order=rng.permutation(cell)
                pivot=len(order)//2
                train[order[:pivot]]=True
                held[order[pivot:]]=True
            a=cell_means(power,condition,train)
            b=cell_means(power,condition,held)
            ti,fi,wt,wf=select_window(a,times,freq)
            tr=a[:,wt,:][:,:,wf].mean(axis=(1,2))
            te=b[:,wt,:][:,:,wf].mean(axis=(1,2))
            splits.append({"split":split,"time_s":float(times[ti]),
                           "freq_hz":float(freq[fi]),
                           "train_interaction":float(tr@WEIGHTS),
                           "heldout_interaction":float(te@WEIGHTS),
                           "train_pooled":float(tr.mean()),
                           "heldout_pooled":float(te.mean())})
        results.append({"subject_id":subject,"status":"COMPLETE",
                        "trial_counts":counts,"n_splits":len(splits),
                        "mean_train_interaction":float(np.mean([s["train_interaction"] for s in splits])),
                        "mean_heldout_interaction":float(np.mean([s["heldout_interaction"] for s in splits])),
                        "selected_windows":splits})
    complete=[x for x in results if x["status"]=="COMPLETE"]
    return {"method":"INDEPENDENT_POST_PREPROCESSING_CROSSFIT_NOT_ORIGINAL_REPLAY",
            "subjects_input":len(set(subject_id)),"subjects_complete":len(complete),
            "subject_level_mean_train_interaction":
                float(np.mean([x["mean_train_interaction"] for x in complete])) if complete else None,
            "subject_level_mean_heldout_interaction":
                float(np.mean([x["mean_heldout_interaction"] for x in complete])) if complete else None,
            "results":results}

def synthetic_fixture(seed=912):
    rng=np.random.default_rng(seed)
    times=np.linspace(-.5,1.5,41)
    freq=np.linspace(4,20,33)
    n=6
    power=rng.normal(size=(n*4*12,len(times),len(freq)))
    subject_id=np.repeat([f"SYN_{i:02}" for i in range(n)],4*12)
    condition=np.tile(np.repeat(CONDITIONS,12),n)
    trial_id=np.tile([f"trial_{i:04}" for i in range(4*12)],n)
    return power,condition,subject_id,trial_id,times,freq

def self_test():
    y,c,s,t,ts,fs=synthetic_fixture()
    x=run_crossfit(y,c,s,t,ts,fs,n_splits=4)
    assert x["subjects_complete"]==6
    assert all(q["n_splits"]==4 for q in x["results"])
    assert x==run_crossfit(y,c,s,t,ts,fs,n_splits=4)
    bad=c.copy()
    bad[np.where(s=="SYN_00")[0][:12]]="active_fixed"
    assert run_crossfit(y,bad,s,t,ts,fs,n_splits=2)["subjects_complete"]==5
    for invalid,match in [
        ((y,c,s,np.array(["same"]*len(t)),ts,fs),"duplicate"),
        ((y,c,s,t,ts[::-1],fs),"strictly")
    ]:
        try:
            run_crossfit(*invalid)
            raise AssertionError("invalid data accepted")
        except ValueError as e:
            assert match in str(e)
    return {"status":"PASS","checks":6,"synthetic_example":
            {k:v for k,v in x.items() if k!="results"}}

def main():
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--npz",type=Path,help="preprocessed power, condition, subject_id, trial_id, times, frequencies")
    parser.add_argument("--seed",type=int,default=20261122)
    parser.add_argument("--splits",type=int,default=20)
    parser.add_argument("--receipt",type=Path)
    args=parser.parse_args()
    if args.npz:
        with np.load(args.npz,allow_pickle=False) as z:
            keys=["power","condition","subject_id","trial_id","times","frequencies"]
            if any(k not in z for k in keys):
                raise ValueError(f"missing one of {keys}")
            result=run_crossfit(*[z[k] for k in keys],seed=args.seed,n_splits=args.splits)
        result["provenance"]="UNVERIFIED_EXTERNAL_PREPROCESSED_NOT_ORIGINAL_RAW_EEG"
    else:
        result=self_test()
        result["provenance"]="SYNTHETIC_ONLY"
    out=json.dumps(result,indent=2,sort_keys=True)+"\n"
    print(out)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(out,encoding="utf8")

if __name__=="__main__":
    main()
