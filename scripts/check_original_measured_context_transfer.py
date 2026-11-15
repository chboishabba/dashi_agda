#!/usr/bin/env python3
"""Original same-study mRNA-context measurement comparison with genotype holdout.

Retains only directly measured 9-mer genotype means, never a model-inferred
landscape. Fepb, Arti and dmsC are distinct original assay contexts.
Their correlations are NOT independent-study replication, causal response
laws, or longitudinal morphological attractor tests.
"""
from __future__ import annotations
import argparse
import csv
import hashlib
import io
import json
import math
from pathlib import Path

ORIGINAL_BLOB = "151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c"
CONTEXTS = ("Fepb", "Arti", "dmsC")
PAIRS = (("Fepb","Arti"), ("Fepb","dmsC"), ("Arti","dmsC"))
SALT = "dashi-2026-v1"


def source_blob_sha(raw):
    return hashlib.sha1(f"blob {len(raw)}\0".encode() + raw).hexdigest()


def genotype_split(seq):
    h = 2166136261
    for c in SALT + ":" + seq:
        h = ((h ^ ord(c)) * 16777619) & 0xFFFFFFFF
    x = h / 4294967296.
    return "train" if x < .7 else "validation" if x < .85 else "test"


def new_accumulator():
    return {"n":0, "sx":0., "sy":0., "sxx":0., "syy":0., "sxy":0.}


def add_pair(acc, x, y):
    acc["n"] += 1
    acc["sx"] += x
    acc["sy"] += y
    acc["sxx"] += x*x
    acc["syy"] += y*y
    acc["sxy"] += x*y


def finish_pair(acc):
    n=acc["n"]
    if n<2:
        raise ValueError("no sufficient paired original measured genotypes")
    numerator=n*acc["sxy"]-acc["sx"]*acc["sy"]
    dx=n*acc["sxx"]-acc["sx"]**2
    dy=n*acc["syy"]-acc["sy"]**2
    if dx<=0 or dy<=0:
        raise ValueError("degenerate source-context variance")
    return {"paired_measured_genotypes":n,
            "pearson_across_original_measured_genotypes":
                numerator/math.sqrt(dx*dy)}


def readout(raw, require_original_blob=True):
    blob=source_blob_sha(raw)
    if require_original_blob and blob!=ORIGINAL_BLOB:
        raise ValueError("source content is not the pinned original Git blob")
    doc=csv.DictReader(io.StringIO(raw.decode("utf-8")))
    required={"Genotype"} | {f"{name}.{j}" for name in CONTEXTS for j in range(1,4)}
    if not required.issubset(doc.fieldnames or []):
        raise ValueError("missing original source-assay columns")
    classes=("train","validation","test")
    acc={k:{f"{a}-{b}":new_accumulator() for a,b in PAIRS} for k in classes}
    coverage={name:0 for name in CONTEXTS}
    seen=set()
    total=0
    for row in doc:
        seq=(row["Genotype"] or "").strip().upper()
        if len(seq)!=9 or any(c not in "ACGU" for c in seq):
            raise ValueError("source genotype must be a nine-base RNA word")
        if seq in seen:
            raise ValueError("duplicate source genotype")
        seen.add(seq)
        total+=1
        means={}
        for name in CONTEXTS:
            values=[]
            for j in range(1,4):
                raw_value=(row[f"{name}.{j}"] or "").strip()
                if raw_value and raw_value.lower() not in ("nan","na","null"):
                    v=float(raw_value)
                    if not math.isfinite(v):
                        raise ValueError("nonfinite original assay replicate")
                    values.append(v)
            if values:
                means[name]=sum(values)/len(values)
                coverage[name]+=1
        bucket=acc[genotype_split(seq)]
        for a,b in PAIRS:
            if a in means and b in means:
                add_pair(bucket[f"{a}-{b}"], means[a], means[b])
    return {
        "source_git_blob":blob,
        "source_sha256":hashlib.sha256(raw).hexdigest(),
        "total_original_genotype_rows":total,
        "context_measured_genotype_coverage":coverage,
        "genotype_disjoint_split_pairwise":
          {label:{name:finish_pair(pair)
                  for name,pair in block.items()}
           for label,block in acc.items()},
        "same_study_distinct_mrna_contexts":True,
        "independent_replicated_study":False,
        "developmental_attractor_discrimination_established":False,
        "pnf_mutation_performed":False,
    }


def self_test():
    from itertools import product
    stream=io.StringIO()
    writer=csv.writer(stream)
    writer.writerow(["Genotype"] +
                    [f"{c}.{r}" for c in CONTEXTS for r in range(1,4)])
    for bases in product("ACGU",repeat=5):
        seq="AAAA"+"".join(bases)
        g=seq.count("G");c=seq.count("C");u=seq.count("U")
        writer.writerow([seq, 1+.03*g+.04*u, 1.2+.03*g+.04*u, "",
                          .5+.09*g-.04*c, .7+.09*g-.04*c,"",
                          .4+.11*c-.05*u, .6+.11*c-.05*u,""])
    result=readout(stream.getvalue().encode(),require_original_blob=False)
    assert result["total_original_genotype_rows"]==1024
    assert all(result["genotype_disjoint_split_pairwise"][split]
               for split in ("train","validation","test"))
    assert result["pnf_mutation_performed"] is False
    print("PASS: source-scoped genotype split and measured 3-context pairing")
    print("SYNTHETIC SELF-TEST; real result requires pinned source CSV")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original-csv",type=Path)
    p.add_argument("--receipt",type=Path)
    p.add_argument("--self-test",action="store_true")
    args=p.parse_args()
    if args.self_test:
        self_test()
        return
    if args.original_csv is None or args.receipt is None:
        p.error("provide --original-csv and --receipt")
    result=readout(args.original_csv.read_bytes())
    args.receipt.write_text(json.dumps(result,indent=2,sort_keys=True)+"\n")
    print(json.dumps(result["genotype_disjoint_split_pairwise"],indent=2))


if __name__=="__main__":
    main()
