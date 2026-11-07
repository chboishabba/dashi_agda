#!/usr/bin/env python3
"""Source-first matched spatial BH4/BH2 measurements and transport scope.

Pairs intracellular/extracellular or region-specific BH4 and BH2 concentrations
with ORIGINAL volumes, specimen IDs, experimental groups and measurement times.
A transport edge is only a CANDIDATE unless independently source-verified.
No reaction/vascular flux is inferred from mere concentration gradients.
"""
from __future__ import annotations

import argparse
import csv
import hashlib
import json
import tempfile
from collections import defaultdict
from decimal import Decimal, InvalidOperation
from pathlib import Path

REQUIRED = (
    "source_id", "original_source_sha256", "experiment_id", "specimen_id",
    "split", "time_s", "region", "compartment", "volume_l",
    "bh4_mol_l", "bh2_mol_l",
    "delivery_connection_id", "delivery_mode", "delivery_source_reference",
)
MODES = {
    "local_diffusion", "vascular_perfusion", "plasma_membrane",
    "interstitial", "gap_junction", "blood_brain_barrier",
}


def number(value, field, *, strictly_positive=False):
    try:
        x = Decimal(value)
    except (InvalidOperation, TypeError) as exc:
        raise ValueError(f"invalid {field}") from exc
    if not x.is_finite() or x < 0 or (strictly_positive and x == 0):
        raise ValueError(f"invalid {field} (finite and nonnegative required)")
    return x


def read_assay(path):
    raw = Path(path).read_bytes()
    with Path(path).open(newline="", encoding="utf-8") as handle:
        reader = csv.DictReader(handle)
        if not set(REQUIRED).issubset(reader.fieldnames or []):
            raise ValueError("missing spatial measurement and source columns")
        rows = list(reader)
    if not rows:
        raise ValueError("empty spatial source assay")
    sources, experiments, specimens, keyed = set(), {}, {}, {}
    for row in rows:
        sha = row["original_source_sha256"].strip().lower()
        if len(sha) != 64 or any(ch not in "0123456789abcdef" for ch in sha):
            raise ValueError("original source SHA256 malformed")
        src, exp, specimen, split = (
            row["source_id"].strip(), row["experiment_id"].strip(),
            row["specimen_id"].strip(), row["split"].strip().lower()
        )
        if not src or not exp or not specimen or split not in {
            "train", "validation", "test"
        }:
            raise ValueError("source, group, specimen and split required")
        region, compartment = (
            row["region"].strip(), row["compartment"].strip()
        )
        edge, mode, flow_ref = (
            row["delivery_connection_id"].strip(),
            row["delivery_mode"].strip(), row["delivery_source_reference"].strip()
        )
        if not region or not compartment or not edge or not flow_ref:
            raise ValueError("region, compartment and route provenance required")
        if mode not in MODES:
            raise ValueError("unknown transport mechanism")
        t = number(row["time_s"], "time_s")
        volume = number(row["volume_l"], "volume_l", strictly_positive=True)
        bh4 = number(row["bh4_mol_l"], "bh4_mol_l")
        bh2 = number(row["bh2_mol_l"], "bh2_mol_l")
        sources.add((src, sha))
        if exp in experiments and experiments[exp] != (src, sha, split):
            raise ValueError("experiment crossed source or train/test boundary")
        experiments[exp] = src, sha, split
        if specimen in specimens and specimens[specimen] != (src, sha, exp, split):
            raise ValueError("specimen reused between experiments or splits")
        specimens[specimen] = src, sha, exp, split
        key = (specimen, t, region, compartment)
        if key in keyed:
            raise ValueError("duplicate specimen-time-region-compartment record")
        keyed[key] = {
            "bh4_mol": bh4 * volume,
            "bh2_mol": bh2 * volume,
            "bh4_mol_l": bh4,
            "bh2_mol_l": bh2,
            "volume_l": volume,
            "transport_connection": edge,
            "transport_mode": mode,
            "transport_reference": flow_ref,
            "experiment": exp,
            "split": split,
        }
    if len(sources) != 1:
        raise ValueError("mixed source assays cannot be pooled")
    per_specimen_times = defaultdict(set)
    groups = defaultdict(set)
    for specimen, t, region, compartment in keyed:
        per_specimen_times[specimen].add(t)
        groups[(specimen, t)].add((region, compartment))
    for specimen, times in per_specimen_times.items():
        if len(times) < 2:
            raise ValueError("longitudinal specimen requires >=2 measured times")
        for t in times:
            if len(groups[(specimen, t)]) < 2:
                raise ValueError("each time needs >=2 distinct source regions")
    if len({exp for exp, (_, _, split) in experiments.items()
            if split == "test"}) < 2:
        raise ValueError("requires >=2 original held-out test experiments")
    same_context_pairs = sum(
        len(locations) * (len(locations) - 1) // 2
        for locations in groups.values()
    )
    return keyed, {
        "status": "source-matched-spatial-observation-not-kinetic-mechanism",
        "original_source": list(sources)[0][0],
        "original_source_sha256_declared": list(sources)[0][1],
        "original_source_digest_verified_by_independent_fetch": False,
        "original_csv_sha256": hashlib.sha256(raw).hexdigest(),
        "original_measurement_rows": len(rows),
        "independent_specimens": len(specimens),
        "independent_test_experiments": len({
            exp for exp, (_, _, split) in experiments.items()
            if split == "test"
        }),
        "source_matched_time_and_region_pairs": same_context_pairs,
        "amount_calculated_from_concentration_and_volume": True,
        "transport_mode_claim_independently_validated": False,
        "flux_inferred_from_concentration_difference": False,
        "independently_calibrated_turnover_rates": False,
        "same_source_29x12_flux_paid": False,
        "pnf_mutation_performed": False,
    }


def report(path):
    rows, receipt = read_assay(path)
    # Report raw matched amounts separately, do NOT aggregate across
    # locations as a stand-in for enzymatic accessibility.
    receipt["context_measurements"] = [
        {
            "specimen": specimen, "time_s": str(t), "region": region,
            "compartment": compartment,
            "bh4_amount_mol": str(v["bh4_mol"]),
            "bh2_amount_mol": str(v["bh2_mol"]),
            "bh4_bh2_local_ratio": (
                str(v["bh4_mol_l"] / v["bh2_mol_l"])
                if v["bh2_mol_l"] > 0 else None
            ),
            "connection_id": v["transport_connection"],
            "transport_mode": v["transport_mode"],
            "transport_source_reference": v["transport_reference"],
            "experiment": v["experiment"],
            "split": v["split"],
        }
        for (specimen, t, region, compartment), v in sorted(rows.items())
    ]
    return receipt


def self_test():
    with tempfile.TemporaryDirectory() as dirname:
        p = Path(dirname) / "synthetic-spatial.csv"
        with p.open("w", newline="") as output:
            writer = csv.writer(output)
            writer.writerow(REQUIRED)
            for exp in range(4):
                split = "train" if exp < 2 else "test"
                for t in (0, 5):
                    for region, compartment, bh4, bh2 in (
                        ("blood", "plasma", "0.000002", "0.000001"),
                        ("endothelium", "cytosol", "0.000001", "0.000002"),
                    ):
                        writer.writerow((
                            "SYNTHETIC:NO-ASSAY", "a" * 64, str(exp),
                            f"specimen-{exp}", split, t, region, compartment,
                            "0.001", bh4, bh2, "blood-endothelium",
                            "plasma_membrane", "synthetic-not-source",
                        ))
        result = report(p)
        assert result["original_measurement_rows"] == 16
        assert result["independent_test_experiments"] == 2
        assert result["source_matched_time_and_region_pairs"] == 8
        assert result["context_measurements"][0]["bh4_amount_mol"] == "2E-9"
        # Fail closed when a specimen leaks between independent experiments.
        with p.open("a", newline="") as output:
            csv.writer(output).writerow((
                "SYNTHETIC:NO-ASSAY", "a" * 64, "3", "specimen-0",
                "test", "6", "blood", "plasma", "0.001", "0.1", "0.1",
                "blood-endothelium", "plasma_membrane", "fake",
            ))
        try:
            read_assay(p)
        except ValueError:
            pass
        else:
            raise AssertionError("specimen leakage admitted")
        print("PASS: same-source/time/region BH4/BH2 amount and route scope")
        print("SYNTHETIC ONLY; no flux or clinical mechanism accepted")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--assay", type=Path)
    parser.add_argument("--receipt", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.assay is None or args.receipt is None:
        parser.error("real --assay and --receipt required")
    result = report(args.assay)
    args.receipt.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n")
    print(json.dumps({
        "status": result["status"],
        "csv_sha256": result["original_csv_sha256"],
        "measured_rows": result["original_measurement_rows"],
    }, sort_keys=True))


if __name__ == "__main__":
    main()
