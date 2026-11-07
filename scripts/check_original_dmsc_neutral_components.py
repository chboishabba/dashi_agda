#!/usr/bin/env python3
"""Descriptive tolerance-graph census for directly measured dmsC nine-mers.

No inferred-genotype values, no auto-definition of experimental neutrality,
no promotion of connected components to developmental attractors.
Default tolerances .05/.10/.20 are exploratory on mean original dmsC scale.
Provenance pins upstream Git blob 151cd87272cbdd6bcc2b1e70bdfd2a4ea2933d2c.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import math
from pathlib import Path

SLOTS = 4**9
ALPHABET = {"A":0,"C":1,"G":2,"U":3}
FEATURES = ("dmsC.1","dmsC.2","dmsC.3")
DEFAULT_TOLERANCES=(.05,.10,.20)


def index_for(seq):
    if len(seq)!=9 or any(ch not in ALPHABET for ch in seq):
        raise ValueError("expected original nine-base RNA genotype")
    x=0
    for ch in seq:
        x=x*4+ALPHABET[ch]
    return x


def data(path):
    original=Path(path).read_bytes()
    values=[None]*SLOTS
    rep_hist={k:0 for k in range(4)}
    seen=set()
    with Path(path).open(newline="") as f:
        source=csv.DictReader(f)
        if not {"Genotype",*FEATURES}.issubset(source.fieldnames or []):
            raise ValueError("missing original dmsC genotype/replicate fields")
        for row in source:
            i=index_for((row["Genotype"] or "").strip().upper())
            if i in seen:
                raise ValueError("duplicate original source genotype")
            seen.add(i)
            observations=[]
            for column in FEATURES:
                value=(row[column] or "").strip()
                if value and value.lower() not in ("nan","na","null"):
                    x=float(value)
                    if not math.isfinite(x):
                        raise ValueError("nonfinite measured replicate")
                    observations.append(x)
            rep_hist[len(observations)]+=1
            if observations:
                values[i]=sum(observations)/len(observations)
    return values,rep_hist,hashlib.sha256(original).hexdigest()


class DisjointSet:
    def __init__(self, observed):
        self.parent=[i if present else -1
                     for i,present in enumerate(observed)]
        self.size=[1 if present else 0 for present in observed]
        self.n_components=sum(observed)
    def root(self,x):
        p=self.parent
        while p[x]!=x:
            p[x]=p[p[x]]
            x=p[x]
        return x
    def join(self,a,b):
        x,y=self.root(a),self.root(b)
        if x==y:return
        p,s=self.parent,self.size
        if s[x]<s[y]:x,y=y,x
        p[y]=x
        s[x]+=s[y]
        self.n_components-=1
    def summarize(self):
        comps=sorted((self.size[i] for i,p in enumerate(self.parent)
                      if i==p),reverse=True)
        return {
            "components":len(comps),
            "singletons":sum(k==1 for k in comps),
            "largest_size":comps[0] if comps else 0,
            "top_five_sizes":comps[:5],
        }


def census(values,tolerances=DEFAULT_TOLERANCES):
    eps=tuple(sorted(set(tolerances)))
    if not eps or any(not math.isfinite(x) or x<0 for x in eps):
        raise ValueError("tolerances must be finite and nonnegative")
    observed=[v is not None for v in values]
    sets=[DisjointSet(observed) for _ in eps]
    edges=[0]*len(eps)
    possible=0
    # Each undirected Hamming-one edge is encountered once: alt > digit.
    for i,yi in enumerate(values):
        if yi is None:continue
        for power in (4**k for k in range(9)):
            digit=(i//power)%4
            for alt in range(digit+1,4):
                j=i+(alt-digit)*power
                yj=values[j]
                if yj is None:continue
                possible+=1
                diff=abs(yi-yj)
                for k,e in enumerate(eps):
                    if diff<=e:
                        edges[k]+=1
                        sets[k].join(i,j)
    result=[]
    n=sum(observed)
    for e,edge_count,ds in zip(eps,edges,sets):
        summary=ds.summarize()
        summary.update({
            "epsilon":e,
            "measured_hamming_one_edges_retained":edge_count,
            "largest_fraction":summary["largest_size"]/n if n else None,
        })
        result.append(summary)
    return {
        "observed_genotypes":n,
        "original_hamming_one_possible_edges":9*3*SLOTS//2,
        "measured_hamming_one_possible_edges":possible,
        "tolerance_net_components":result,
        "thresholds_are_exploratory_not_source_calibrated":True,
        "connected_components_are_not_phenotype_equality_or_attractor_basins":True,
    }


def self_test():
    values=[None]*SLOTS
    for seq,val in [("AAAAAAAAA",0.),("AAAAAAAAC",.05),
                    ("AAAAAAAAG",.12)]:
        values[index_for(seq)]=val
    r=census(values,(.01,.10))
    assert r["observed_genotypes"]==3
    assert r["measured_hamming_one_possible_edges"]==3
    assert r["tolerance_net_components"][0]["components"]==3
    assert r["tolerance_net_components"][1]["components"]==1
    print("PASS: 9-mer Hamming-1 edges, measured-only tolerance networks")
    print("SYNTHETIC SELF-TEST; real genotype landscape still needs original CSV")


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--original-csv",type=Path)
    p.add_argument("--output",type=Path)
    p.add_argument("--self-test",action="store_true")
    a=p.parse_args()
    if a.self_test:self_test();return
    if not a.original_csv or not a.output:
        p.error("--original-csv and --output required")
    values,rep_hist,sha=data(a.original_csv)
    report=census(values)
    report.update({"source_sha256":sha,
                   "original_replicate_count_by_genotype":rep_hist,
                   "pnf_mutation_performed":False})
    a.output.write_text(json.dumps(report,sort_keys=True,indent=2)+"\n")
    print(json.dumps({"source_sha256":sha,
                      "components":report["tolerance_net_components"]},indent=2))


if __name__=="__main__":
    main()
