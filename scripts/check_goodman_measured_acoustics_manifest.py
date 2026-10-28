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
import math
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
    if not isinstance(scenarios, list) or len(scenarios) != 4 or {r.get("id") for r in scenarios} != SCENARIOS:
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
        if not isinstance(row, dict):
            raise ValueError("position records must be objects")
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


def enforce_spatial_buffer(rows, assigned, minimum_separation_m):
    """Check metric source separation with a deterministic 3-D spatial hash.

    Within each acquisition scenario, any pair assigned to distinct
    partitions at Euclidean distance below the threshold causes rejection.
    Bins have edge length equal to threshold. Any offending pair lies
    in the same or one of the 26 adjacent bins. Checks scale with local
    occupancy, not the square of the full 13,377-position corpus.
    R2 is intentionally isolated as the external environment test.
    """
    if not math.isfinite(minimum_separation_m) or minimum_separation_m <= 0:
        raise ValueError("positive physical separation threshold required")
    by_group = {(x["scenario"], x["spatial_block"]): x["partition"] for x in assigned}
    positions = {}
    for row in rows:
        sc = row.get("scenario")
        pos = str(row.get("position_id", ""))
        block = str(row.get("spatial_block", ""))
        coords = row.get("xyz_m")
        if not isinstance(coords, list) or len(coords) != 3:
            raise ValueError("physical xyz_m source coordinates required")
        if not all(type(v) in (float, int) and math.isfinite(v) for v in coords):
            raise ValueError("invalid metric coordinates")
        key = (sc, pos)
        partition = by_group.get((sc, block))
        if partition is None:
            raise ValueError("source block absent from partition map")
        datum = (tuple(coords), partition)
        if key in positions and positions[key] != datum:
            raise ValueError("inconsistent position coordinates or partition")
        positions[key] = datum

    buckets = {}
    for (sc, _), (xyz, partition) in sorted(positions.items()):
        if partition == "external_environment":
            continue
        cell = tuple(math.floor(v / minimum_separation_m) for v in xyz)
        for dx in (-1, 0, 1):
            for dy in (-1, 0, 1):
                for dz in (-1, 0, 1):
                    neighbor = (sc, cell[0]+dx, cell[1]+dy, cell[2]+dz)
                    for other_xyz, other_partition in buckets.get(neighbor, ()):
                        if partition != other_partition and math.dist(xyz, other_xyz) < minimum_separation_m:
                            raise ValueError("cross-partition spatial buffer violated")
        buckets.setdefault((sc, *cell), []).append((xyz, partition))

def validate_position_completeness(positions):
    """Require the exact source-identity inventory, not just the row count."""
    expected_counts = {"A1": 4096, "A2": 4096, "D1": 1089, "R2": 4096}
    if not isinstance(positions, list) or any(not isinstance(p, dict) for p in positions):
        raise ValueError("position table must be an array of records")
    if len(positions) != 13377:
        raise ValueError("expected exactly 13,377 position records")
    observed = {(row.get("scenario"), str(row.get("position_id"))) for row in positions}
    if len(observed) != 13377:
        raise ValueError("source-position labels must be unique")
    counts = {sc: sum(sc0 == sc for sc0, _ in observed) for sc in expected_counts}
    if counts != expected_counts:
        raise ValueError("source-position counts differ from MIRACLE version 4")
    return counts


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
    p.add_argument("--min-separation-m", type=float, required=True)
    args = p.parse_args()
    manifest = json.loads(Path(args.manifest).read_text())
    validate_manifest(manifest, Path(args.archive_root))
    positions = json.loads(Path(args.positions).read_text())
    if not isinstance(positions, list) or not positions:
        raise ValueError("source-position metadata required")
    validate_position_completeness(positions)
    groups = split_blocks(positions, args.seed)
    enforce_spatial_buffer(positions, groups, args.min_separation_m)
    counts = {partition: sum(len(g["positions"]) for g in groups if g["partition"] == partition)
              for partition in ("train", "validation", "test", "external_environment")}
    if any(counts[name] == 0 for name in counts):
        raise ValueError("incomplete held-out partition: all four partitions need independent groups")
    result = {"dataset_doi": LATEST_DOI, "sha256_verified": True,
              "position_metadata_sha256": digest(Path(args.positions)),
              "partitions": groups, "partition_position_counts": counts,
              "min_separation_m": args.min_separation_m,
              "measurement_results": None,
              "warning": "No calibration/covariance/accuracy measured by manifest and split alone"}
    Path(args.output).write_text(json.dumps(result, indent=2) + "\n")


if __name__ == "__main__":
    main()
