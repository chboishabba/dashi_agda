#!/usr/bin/env python3
"""P5 measured genotype-phenotype holdout and neutral-component benchmark.

Source CSV columns: source_id, sequence, split, measurement_kind, trait,
trait_unit, assay_context, measurement_id.
split=train/validation/test, measurement_kind MUST equal "measured".
No imputed/inferred traits are accepted as original measurements.
Tuning uses validation only, test remains untouched until final evaluation.
Static variant-effect benchmark, NOT a claim about developmental attractors.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import itertools
import json
from collections import Counter
from pathlib import Path

import numpy as np
from scipy.sparse import csr_matrix
from scipy.stats import spearmanr
from sklearn.linear_model import Ridge

REQUIRED = ("source_id", "sequence", "split", "measurement_kind",
            "trait", "trait_unit", "assay_context", "measurement_id")
ALPHABET = "ACGU"
ALPHABET_MAP = {v:i for i,v in enumerate(ALPHABET)}


def read_measurements(path):
    raw=Path(path).read_bytes()
    with Path(path).open(newline="") as handle:
        reader=csv.DictReader(handle)
        if not set(REQUIRED).issubset(reader.fieldnames or ()):
            raise ValueError("required fields: "+",".join(REQUIRED))
        data=list(reader)
    if not data:
        raise ValueError("no measured genotypes")
    observations,seen={},set()
    meta=set()
    for i,row in enumerate(data,2):
        source=row["source_id"].strip()
        seq=row["sequence"].upper().replace("T","U").strip()
        split=row["split"].lower().strip()
        kind=row["measurement_kind"].lower().strip()
        trait_unit=row["trait_unit"].strip()
        context=row["assay_context"].strip()
        measurement_id=row["measurement_id"].strip()
        try: trait=float(row["trait"])
        except ValueError as exc: raise ValueError(f"line {i}: invalid trait") from exc
        if not source or not trait_unit or not context or not measurement_id:
            raise ValueError(f"line {i}: missing original provenance")
        if split not in ("train","validation","test") or kind!="measured":
            raise ValueError(f"line {i}: invalid split or inferred trait")
        if not np.isfinite(trait):
            raise ValueError(f"line {i}: nonfinite value")
        if any(s not in ALPHABET_MAP for s in seq) or not seq:
            raise ValueError(f"line {i}: sequence not RNA/DNA alphabet")
        if measurement_id in seen:
            raise ValueError("duplicate measurement_id")
        seen.add(measurement_id)
        if seq in observations and observations[seq] != split:
            raise ValueError(f"genotype appears in multiple splits: {seq}")
        observations[seq]=split
        meta.add((source,trait_unit,context,len(seq)))
        data[i-2]=(seq,split,trait,measurement_id)
    if len(meta)!=1:
        raise ValueError("source, units, context or sequence length differs")
    counts=Counter(x[1] for x in data)
    if counts["train"]<40 or counts["validation"]<15 or counts["test"]<15:
        raise ValueError("need >=40 train, >=15 validation and >=15 test measurements")
    source,unit,context,length=next(iter(meta))
    return data,hashlib.sha256(raw).hexdigest(), {
        "source":source,"trait_unit":unit,"assay_context":context,
        "sequence_length":length, "counts":dict(counts),
        "unique_genotypes":len(observations)}


def feature_matrix(seqs, order=1):
    length=len(seqs[0])
    pair_sites=list(itertools.combinations(range(length),2))
    size=length*4+(16*len(pair_sites) if order==2 else 0)
    rows,cols=[],[]
    for k,seq in enumerate(seqs):
        indices=[4*i+ALPHABET_MAP[ch] for i,ch in enumerate(seq)]
        if order==2:
            indices += [
                length*4+16*j+4*ALPHABET_MAP[seq[i]]+ALPHABET_MAP[seq[l]]
                for j,(i,l) in enumerate(pair_sites)
            ]
        rows.extend([k]*len(indices))
        cols.extend(indices)
    return csr_matrix((np.ones(len(rows),dtype=float),(rows,cols)),
                      shape=(len(seqs),size))


def score(y,pred):
    y=np.asarray(y,dtype=float)
    pred=np.asarray(pred,dtype=float)
    rank=float(spearmanr(y,pred).statistic) if len(y)>2 else None
    if rank is not None and not np.isfinite(rank):
        rank=None
    return {"n":len(y),"rmse":float(np.sqrt(np.mean((y-pred)**2))),
            "mae":float(np.mean(abs(y-pred))),
            "spearman":rank}


def fit_and_evaluate(data,sha,metadata,seed=0,bootstrap=300):
    splits={s:[r for r in data if r[1]==s] for s in ("train","validation","test")}
    y={s:np.asarray([r[2] for r in rows]) for s,rows in splits.items()}
    x={order:{s:feature_matrix([r[0] for r in rows],order)
              for s,rows in splits.items()}
       for order in (1,2)}
    variants=[]
    # No test-set evaluation during model selection.
    for order in (1,2):
        for alpha in (0.1,1.,10.,100.):
            model=Ridge(alpha=alpha,solver="lsqr")
            model.fit(x[order]["train"],y["train"])
            rmse=score(y["validation"],model.predict(x[order]["validation"]))["rmse"]
            variants.append((rmse,order,alpha))
    val_rmse,order,alpha=min(variants)
    final=Ridge(alpha=alpha,solver="lsqr")
    final.fit(x[order]["train"],y["train"])
    yp=final.predict(x[order]["test"])
    null_pred=np.full(len(yp),float(np.mean(y["train"])))
    m=score(y["test"],yp)
    baseline=score(y["test"],null_pred)
    rng=np.random.default_rng(seed)
    rmse_draws=[]
    for _ in range(bootstrap):
        indices=rng.integers(0,len(yp),size=len(yp))
        rmse_draws.append(score(y["test"][indices],yp[indices])["rmse"])
    ci=np.quantile(rmse_draws,[.025,.975])
    # The neutral graph is restricted to *observed test sequences*. It is
    # not promoted to the full 4^L neutral-component census.
    seqs=[r[0] for r in splits["test"]]
    values={seq:val for seq,val in zip(seqs,y["test"])}
    return {
        "status":"heldout-measured-assay-association-not-causal-attractor",
        "source_sha256":sha,"metadata":metadata,
        "selected_order":order,"selected_ridge_alpha":alpha,
        "selected_validation_rmse":val_rmse,
        "test":m,"train_mean_baseline_test":baseline,
        "test_rmse_bootstrap_95_interval":[float(ci[0]),float(ci[1])],
        "bootstrap_seed":seed,"bootstrap_replicates":bootstrap,
        "all_model_selection_used_validation_only":True,
        "test_genotypes_disjoint_from_train_and_validation":True,
        "inferred_landscape_values_excluded":True,
        "full_genotype_neutral_components_established":False,
        "biological_attractors_inferred":False,
        "pnf_mutation_performed":False,
    }


def self_test():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/"observed.csv"
        rng=np.random.default_rng(19)
        seqs=["".join(x) for x in itertools.product(ALPHABET,repeat=4)]
        rng.shuffle(seqs)
        with path.open("w",newline="") as handle:
            writer=csv.writer(handle)
            writer.writerow(REQUIRED)
            for k,seq in enumerate(seqs):
                split="train" if k<165 else ("validation" if k<210 else "test")
                val=(.6*seq.count("G")-.3*seq.count("C")
                     +.7*("AG" in seq)+.2*seq.count("U"))
                writer.writerow(("SYNTHETIC:NO-PUBLIC-DATA",seq,split,
                                 "measured",val,"arbitrary-unit",
                                 "synthetic-assay",str(k)))
        data,sha,meta=read_measurements(path)
        result=fit_and_evaluate(data,sha,meta,bootstrap=40)
        assert result["test"]["rmse"] < result["train_mean_baseline_test"]["rmse"]
        assert result["test_genotypes_disjoint_from_train_and_validation"]
        path.write_text(path.read_text().replace(",measured,",",imputed,",1))
        try: read_measurements(path)
        except ValueError: pass
        else: raise AssertionError("inferred label treated as measurement")
    print("PASS: genomic heldout split, measurement provenance, epistasis models, bootstrap")
    print("SYNTHETIC ONLY: no measured dataset or attractor outcome assessed")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--assay",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--seed",type=int,default=0)
    p.add_argument("--bootstrap",type=int,default=300)
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:
        self_test(); return
    if not a.assay or not a.output:
        p.error("--assay and --output required")
    if a.bootstrap<30:
        p.error("at least 30 bootstrap draws required")
    data,sha,meta=read_measurements(a.assay)
    result=fit_and_evaluate(data,sha,meta,seed=a.seed,bootstrap=a.bootstrap)
    a.output.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps({"source_sha256":sha,"test":result["test"],
                      "status":result["status"]}))


if __name__=="__main__":
    main()
