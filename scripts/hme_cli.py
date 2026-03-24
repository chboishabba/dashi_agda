#!/usr/bin/env python3
"""
HME CLI: processes DA51 traces → canonical witnesses and clustering metrics.
Does not invoke Agda; produces JSON for downstream import.
"""

import argparse
import json
import sys
import numpy as np

from hme_pipeline import (
    DA51Trace,
    canonical_witness,
    kmeans,
    silhouette_score,
    invariance_score,
    process_trace,
    normalize,
)


def load_traces(path: str):
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    traces = []
    for t in data:
        traces.append(
            DA51Trace(
                id=t["id"],
                exponents=t["exponents"],
                hot=t.get("hot", 0),
                cold=t.get("cold", 0),
                basin=t.get("basin", 0),
                j_fixed=t.get("j_fixed", False),
            )
        )
    return traces


def load_attractors(path: str, dim: int):
    with open(path, "r", encoding="utf-8") as f:
        data = json.load(f)
    return [normalize(np.array(vec, dtype=float)) for vec in data if len(vec) == dim]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("traces", help="JSON file: list of DA51 traces")
    ap.add_argument("--attractors", help="JSON file: list of attractor vectors", default=None)
    ap.add_argument("--k", type=int, default=3, help="k-means clusters")
    ap.add_argument("--threshold", type=float, default=0.9993, help="cone similarity threshold")
    ap.add_argument("--out", help="output JSON file", default="-")
    args = ap.parse_args()

    traces = load_traces(args.traces)
    if not traces:
        print("[]")
        return

    dim = len(traces[0].exponents)
    if args.attractors:
        attractors = load_attractors(args.attractors, dim)
    else:
        attractors = [normalize(np.ones(dim))]

    witnesses = [process_trace(t, attractors[0]) for t in traces]
    inv_score = invariance_score(witnesses)

    cluster_ids = kmeans(traces, k=min(args.k, len(traces)))
    sil = silhouette_score(traces, cluster_ids, k=min(args.k, len(traces)))

    canonical = [
        canonical_witness(t, attractors, threshold=args.threshold).__dict__ for t in traces
    ]

    result = {
        "canonical_witnesses": canonical,
        "cluster_assignments": cluster_ids,
        "silhouette": sil,
        "invariance_score": inv_score,
    }

    if args.out == "-":
        json.dump(result, sys.stdout, indent=2)
    else:
        with open(args.out, "w", encoding="utf-8") as f:
            json.dump(result, f, indent=2)


if __name__ == "__main__":
    main()
