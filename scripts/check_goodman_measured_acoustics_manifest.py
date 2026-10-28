#!/usr/bin/env python3
"""Fail-closed MIRACLE manifest/split/uncertainty protocol; no dataset access.

Original authors: A. Kujawski, A. J. R. Pelling, E. Sarradj (2024).
Paper DOI 10.1186/s13636-024-00352-8. Current archive version DOI:
10.14279/depositonce-20837 (version 4); old version 20106 must NOT mix.
CC BY-NC-SA 4.0. No observed acoustic accuracy is inferred by this tool.
"""
import argparse
import hashlib
import json
from pathlib import Path
from statistics import mean

SCENARIOS = {"A1", "A2", "D1", "R2"}
LATEST_DOI = "10.14279/depositonce-20837"


def digest(path):
    h = hashlib.sha256()
    with open(path, "rb") as stream:
        for chunk in iter(lambda: stream.read(1024 * 1024), b""):
            h.update(chunk)
    return h.hexdigest()


def validate_manifest(manifest, root):
    if manifest.get("dataset_doi") != LATEST_DOI:
        raise ValueError("must pin the current MIRACLE dataset version DOI")
    if manifest.get("license") != "CC BY-NC-SA 4.0":
        raise ValueError("dataset licence must remain attached")
    scenarios = manifest.get("scenarios")
    if not isinstance(scenarios, list) or {r.get("id") for r in scenarios} != SCENARIOS:
        raise ValueError("required four unique scenario entries")
    for rec in scenarios:
        ident = rec["id"]
        path = root / (ident + ".h5")
        expected = rec.get("sha256")
        if not isinstance(expected, str) or len(expected) != 64:
            raise ValueError(f"missing SHA-256 for {ident}")
        if not path.is_file() or digest(path) != expected.lower():
            raise ValueError(f"missing or mismatched archive for {ident}")
    return True


def split_blocks(rows, seed):
    """Deterministic group split. One position ID may never span partitions.

    Group positions by scenario and declared spatial block; all microphone
    channels and repeat recordings for a position stay together. Hash-based
    grouping does not prove physical separation; buffer validation is external.
    """
    blocks = {}
    seen_position_block = {}
    for row in rows:
        sc = row.get("scenario")
        pos = str(row.get("position_id", ""))
        block = str(row.get("spatial_block", ""))
        if sc not in SCENARIOS or not pos or not block:
            raise ValueError("missing scenario, source ID, or spatial block")
        key = (sc, pos)
        if key in seen_position_block and seen_position_block[key] != block:
            raise ValueError("position group crosses spatial blocks")
        seen_position_block[key] = block
        blocks.setdefault((sc, block), []).append(row)
    assigned = {}
    for sc, block in blocks:
        # Entire R2 scenario is an external environment-shift test.
        if sc == "R2":
            label = "external_environment"
        else:
            score = int(hashlib.sha256(f"{seed}:{sc}:{block}".encode()).hexdigest()[:12], 16) % 100
            label = "train" if score < 60 else ("validation" if score < 80 else "test")
        assigned[(sc, block)] = label
    return [{"scenario": sc, "spatial_block": block, "partition": label,
             "positions": sorted({str(x["position_id"]) for x in blocks[(sc, block)]})}
            for (sc, block), label in sorted(assigned.items())]


def correlated_error_budget(pairs, inverse_gain):
    """Sample covariance from independently acquired paired replicate errors.

    No IID assumption about individual waveform points. Input pairs must
    already be *independent calibration units*, not overlapping time frames.
    """
    if len(pairs) < 3:
        raise ValueError("at least three independent paired calibration units required")
    a = [float(p[0]) for p in pairs]
    b = [float(p[1]) for p in pairs]
    if not all(__import__("math").isfinite(v) for v in a + b):
        raise ValueError("non-finite calibration errors")
    ma, mb = mean(a), mean(b)
    n = len(a)
    va = sum((v-ma)**2 for v in a)/(n-1)
    vb = sum((v-mb)**2 for v in b)/(n-1)
    cab = sum((u-ma)*(v-mb) for u,v in zip(a,b))/(n-1)
    r = float(inverse_gain)
    if not __import__("math").isfinite(r):
        raise ValueError("invalid inverse gain")
    difference = va + vb - 2*cab
    if difference < -1e-12:
        raise ValueError("invalid covariance estimate")
    return {"n_independent_units": n, "mean_error": [ma, mb],
            "cov_input": [[va, cab], [cab, vb]],
            "cov_recovered": [[va, r*(cab-va)],
                               [r*(cab-va), r*r*max(0.0, difference)]],
            "bias_recovered": [ma, r*(mb-ma)],
            "provenance": "paired calibration errors supplied by caller; not MIRACLE measured automatically"}


def main():
    p = argparse.ArgumentParser()
    p.add_argument("--manifest", required=True)
    p.add_argument("--archive-root", required=True)
    p.add_argument("--positions", required=True)
    p.add_argument("--seed", default="sonic-heldout-v1")
    p.add_argument("--output", required=True)
    args = p.parse_args()
    manifest = json.loads(Path(args.manifest).read_text())
    validate_manifest(manifest, Path(args.archive_root))
    positions = json.loads(Path(args.positions).read_text())
    if not isinstance(positions, list) or not positions:
        raise ValueError("source-position metadata required")
    groups = split_blocks(positions, args.seed)
    result = {"dataset_doi": LATEST_DOI, "sha256_verified": True,
              "partitions": groups, "measurement_results": None,
              "warning": "No calibration/covariance/accuracy measured by manifest and split alone"}
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
