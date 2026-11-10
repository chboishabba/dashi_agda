#!/usr/bin/env python3
"""Dual-reviewer GCC source-frame comparison, with coding-uncertainty bounds.

Uses the original source-byte verified single-coder consumer twice,
retaining article identity. The two observed frame labels must be made
by distinct coders. Article-level disagreements produce a finite bound
on the DESCRIPTIVE four-cell DiD across either coder's interpretation,
not a causal confidence interval. Actual original article bytes and
source-backed intervention time remain mandatory on production runs.
"""
from __future__ import annotations

import argparse
from collections import Counter
import json
from pathlib import Path
import check_ccdcoe_p3_sampling_frame as census
from tempfile import TemporaryDirectory
import hashlib

import measure_ccdcoe_p3_gcc_media as base

DUAL_REQUIRED = {"second_coder_id", "second_frame", "second_review_receipt"}


def analyse_dual(rows: list[dict], focus: str, intervention_date: str,
                 intervention_receipt: str, source_root: Path | None = None,
                 synthetic_fixture: bool = False) -> dict:
    if not rows:
        raise ValueError("No actual article rows")
    reviewer_panel = None
    for row in rows:
        if not DUAL_REQUIRED <= row.keys():
            raise ValueError("Second independent coding receipt required")
        if not isinstance(row["second_coder_id"], str) or not row["second_coder_id"].strip():
            raise ValueError("Second reviewer ID must be a nonempty string")
        if row["second_coder_id"] == row.get("coder_id"):
            raise ValueError("Coding must be independently attributed")
        if not isinstance(row["second_review_receipt"], str) or not row["second_review_receipt"].strip():
            raise ValueError("Second reviewer receipt must be a nonempty string")
        if row["second_review_receipt"] == row.get("review_receipt"):
            raise ValueError("Two reviewer observations must have distinct review receipts")
        panel = (row.get("coder_id"), row["second_coder_id"])
        if reviewer_panel is None:
            reviewer_panel = panel
        if panel != reviewer_panel:
            raise ValueError("Pooled Scott pi requires a stable ordered reviewer panel")
        if row["second_frame"] not in base.FRAMES:
            raise ValueError("Second coding frame must be valid")
        if not synthetic_fixture and "SYNTHETIC" in str(row["second_review_receipt"]).upper():
            raise ValueError("Synthetic second-coder receipt not admissible")
    first = base.analyse(rows, focus, intervention_date, intervention_receipt,
                         source_root=source_root,
                         synthetic_fixture=synthetic_fixture)
    others = [{**r, "coder_id": r["second_coder_id"],
               "review_receipt": r["second_review_receipt"],
               "frame": r["second_frame"]} for r in rows]
    second = base.analyse(others, focus, intervention_date,
                          intervention_receipt, source_root=source_root,
                          synthetic_fixture=synthetic_fixture)
    agreement = sum(row["frame"] == row["second_frame"] for row in rows)
    n = len(rows)
    counts = Counter(
        frame for row in rows
        for frame in (row["frame"], row["second_frame"]))
    chance = sum((counts[label] / (2 * n))**2 for label in base.FRAMES)
    observed = agreement / n
    # With one pooled category, expected agreement is one and Scott's pi
    # has a zero denominator. Perfect raw agreement does not make pi = 1.
    pi = (observed - chance) / (1 - chance) if chance < 1 else None

    bounds: dict[str, dict] = {}
    for arm in sorted(base.ARMS):
        for period in sorted(base.PERIODS):
            cell_rows = [r for r in rows if
                         r["treatment"] == arm and r["period"] == period]
            if not cell_rows:
                raise ValueError("Unobserved treatment/comparison period")
            both = sum(r["frame"] == focus and
                       r["second_frame"] == focus for r in cell_rows)
            either = sum(r["frame"] == focus or
                         r["second_frame"] == focus for r in cell_rows)
            bounds[f"{arm}:{period}"] = {
                "reviewed_documents": len(cell_rows),
                "both_coders_identify_frame": both,
                "either_coder_identifies_frame": either,
                "lower_share": round(both / len(cell_rows), 6),
                "upper_share": round(either / len(cell_rows), 6),
            }
    def rng(arm: str, period: str) -> tuple[float, float]:
        rs = [r for r in rows if r["treatment"] == arm and r["period"] == period]
        return (sum(r["frame"] == focus and r["second_frame"] == focus for r in rs) / len(rs),
                sum(r["frame"] == focus or r["second_frame"] == focus for r in rs) / len(rs))

    a, b = rng("GCC-linked-outlet", "after")
    c, d = rng("GCC-linked-outlet", "before")
    e, f = rng("comparison-outlet", "after")
    g, h = rng("comparison-outlet", "before")
    # Four independent interval extrema of the descriptive DiD:
    # T_after - T_before - C_after + C_before.
    did_lower = a - d - f + g
    did_upper = b - c - e + h
    if did_lower > did_upper:
        raise AssertionError("Coding interval arithmetic error")
    return {
        "schema": "dashi.ccdcoe.p3.gcc_dual_coder.v1",
        "observed_rows": n,
        "source_bytes_verified": not synthetic_fixture,
        "focus": focus,
        "raw_coding_agreement": round(observed, 6),
        "scott_pi_five_frame_categories": None if pi is None else round(pi, 6),
        "scott_pi_defined": pi is not None,
        "coding_disagreements": n - agreement,
        "frame_share_bounds_by_cell": bounds,
        "descriptive_did_coder1": first["descriptive_difference_in_differences"],
        "descriptive_did_coder2": second["descriptive_difference_in_differences"],
        "descriptive_did_partial_coding_interval":
            [round(did_lower, 6), round(did_upper, 6)],
        "historical_original_authenticity_established": False,
        "reviewer_independence_authenticated": False,
        "stable_ordered_reviewer_panel": list(reviewer_panel),
        "causal_effect": None,
        "causal_attribution": "NOT_IDENTIFIED",
        "interpretation": "Agreement and finite coding-ambiguity bounds; no sampling, outlet-cluster, time-series or causal confidence interval",
    }


def self_test() -> None:
    rows = []
    with TemporaryDirectory() as td:
        root = Path(td)
        for arm in sorted(base.ARMS):
            for period in sorted(base.PERIODS):
                for i in range(3):
                    rid = f"synthetic-{arm}-{period}-{i}"
                    (root / (rid + ".txt")).write_bytes(rid.encode())
                    frame = "science_uncertainty" if (
                        i == 0 or (arm == "GCC-linked-outlet" and period == "after")
                    ) else "other_or_undetermined"
                    rows.append({
                        "id": rid, "source_file": rid + ".txt",
                        "source_sha256": hashlib.sha256(rid.encode()).hexdigest(),
                        "outlet": "LOCAL-FIXTURE-" + arm,
                        "date": "1992-01-01" if period == "before" else "1994-01-01",
                        "treatment": arm, "period": period, "frame": frame,
                        "second_frame": frame, "source_text_reviewed": True,
                        "coder_id": "fixture-reviewer-A",
                        "second_coder_id": "fixture-reviewer-B",
                        "review_receipt": "LOCAL-TEST-A",
                        "second_review_receipt": "LOCAL-TEST-B",
                    })
        kwargs = dict(intervention_date="1993-01-01",
                      intervention_receipt="LOCAL-FIXTURE-ONSET",
                      source_root=root)
        matched = analyse_dual(rows, "science_uncertainty", **kwargs)
        assert matched["observed_rows"] == 12
        assert matched["scott_pi_five_frame_categories"] == 1.0
        assert matched["descriptive_did_partial_coding_interval"] == [
            0.666667, 0.666667]
        # Two coders can agree on every article but use only one category.
        # This yields raw agreement 1, while Scott's pi is undefined (0/0).
        constant = [{**row, "frame": "science_uncertainty",
                     "second_frame": "science_uncertainty"} for row in rows]
        degenerate = analyse_dual(constant, "science_uncertainty", **kwargs)
        assert degenerate["raw_coding_agreement"] == 1.0
        assert degenerate["scott_pi_five_frame_categories"] is None
        assert degenerate["scott_pi_defined"] is False
        assert degenerate["coding_disagreements"] == 0
        assert degenerate["descriptive_did_partial_coding_interval"] == [0.0, 0.0]
        changed = [dict(r) for r in rows]
        changed[0]["second_frame"] = (
            "other_or_undetermined" if changed[0]["frame"] ==
            "science_uncertainty" else "science_uncertainty")
        disputed = analyse_dual(changed, "science_uncertainty", **kwargs)
        assert disputed["coding_disagreements"] == 1
        assert disputed["descriptive_did_partial_coding_interval"][0] <= (
            disputed["descriptive_did_coder2"])
        assert disputed["descriptive_did_partial_coding_interval"][1] >= (
            disputed["descriptive_did_coder1"])
        bad = [dict(r) for r in rows]
        bad[0]["second_review_receipt"] = bad[0]["review_receipt"]
        try:
            analyse_dual(bad, "science_uncertainty", **kwargs)
        except ValueError as exc:
            assert "distinct review receipts" in str(exc)
        else:
            raise AssertionError("Recycled reviewer receipt accepted as independent coding")
        for bogus in (" ", 1, None):
            bad = [dict(r) for r in rows]
            bad[0]["second_review_receipt"] = bogus
            try:
                analyse_dual(bad, "science_uncertainty", **kwargs)
            except ValueError as exc:
                assert "nonempty string" in str(exc)
            else:
                raise AssertionError("Nontextual second reviewer receipt admitted")
        bad = [dict(r) for r in rows]
        bad[0]["second_coder_id"] = bad[0]["coder_id"]
        try:
            analyse_dual(bad, "science_uncertainty", **kwargs)
        except ValueError:
            pass
        else:
            raise AssertionError("Same person given two independent coding roles")
        bad = [dict(r) for r in rows]
        bad[0]["second_coder_id"] = "fixture-reviewer-C"
        try:
            analyse_dual(bad, "science_uncertainty", **kwargs)
        except ValueError as e:
            assert "stable ordered reviewer panel" in str(e)
        else:
            raise AssertionError("Reviewer-panel drift admitted into pooled agreement")
        bad = [dict(r) for r in rows]
        bad[0]["coder_id"] = "fixture-reviewer-C"
        try:
            analyse_dual(bad, "science_uncertainty", **kwargs)
        except ValueError as e:
            assert "stable ordered reviewer panel" in str(e)
        else:
            raise AssertionError("First reviewer-panel drift admitted")
        bad = [dict(r) for r in rows]
        bad[0]["source_sha256"] = "a" * 64
        try:
            analyse_dual(bad, "science_uncertainty", **kwargs)
        except ValueError:
            pass
        else:
            raise AssertionError("Unverified original file admitted")
    print("PASS: independent attribution, degenerate Scott pi undefined, coding ambiguity bounds, source bytes and negative fixtures")


def main() -> None:
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("--self-test", action="store_true")
    p.add_argument("--input", type=Path)
    p.add_argument("--output", type=Path)
    p.add_argument("--source-root", type=Path)
    p.add_argument("--frame", type=Path, help="Predeclared full eligible article census JSON")
    p.add_argument("--expected-frame-sha256", required=False,
                   help="Digest of pre-registered frame independently retained before coding")
    p.add_argument("--intervention-date")
    p.add_argument("--intervention-receipt")
    p.add_argument("--focus", default="science_uncertainty")
    args = p.parse_args()
    if args.self_test:
        self_test()
        return
    if not all((args.input, args.output, args.source_root, args.frame, args.expected_frame_sha256,
                args.intervention_date, args.intervention_receipt)):
        p.error("All source root, date, receipt, input and output arguments required")
    rows = [json.loads(line) for line in args.input.read_text(
        encoding="utf-8").splitlines() if line.strip()]
    frame_audit = census.check(json.loads(args.frame.read_text(encoding="utf-8")), rows,
                 args.expected_frame_sha256,
                 args.intervention_date, args.intervention_receipt)
    result = analyse_dual(
        rows, args.focus, args.intervention_date,
        args.intervention_receipt, source_root=args.source_root)
    result["sampling_frame_audit"] = frame_audit
    args.output.parent.mkdir(parents=True, exist_ok=True)
    args.output.write_text(json.dumps(result, indent=2, sort_keys=True) + "\n",
                           encoding="utf-8")
    print("Dual-coded original source summary saved; causal effect NOT IDENTIFIED")


if __name__ == "__main__":
    main()
