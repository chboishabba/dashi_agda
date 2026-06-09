from __future__ import annotations

import csv
import json
import subprocess
import sys
from pathlib import Path


SCRIPT = Path("scripts/ym_sprint91_wc3_new_math_audit.py")
RECEIPT = Path(
    "DASHI/Physics/Closure/YMSprint91WC3NewMathReceipt.agda"
)


def run_audit(tmp_path: Path, repo_root: Path | None = None) -> tuple[Path, dict]:
    out_dir = tmp_path / "ym_sprint91_wc3_new_math"
    cmd = [sys.executable, str(SCRIPT), "--out-dir", str(out_dir)]
    if repo_root is not None:
        cmd.extend(["--repo-root", str(repo_root)])
    subprocess.run(cmd, check=True, cwd=Path.cwd())
    summary = json.loads(
        (out_dir / "ym_sprint91_wc3_new_math_summary.json").read_text()
    )
    return out_dir, summary


def read_csv(path: Path) -> list[dict[str, str]]:
    with path.open(newline="") as handle:
        return list(csv.DictReader(handle))


def write_synthetic_receipt(repo_root: Path) -> None:
    receipt = repo_root / RECEIPT
    receipt.parent.mkdir(parents=True)
    receipt.write_text(
        "\n".join(
            [
                "module DASHI.Physics.Closure.YMSprint91WC3NewMathReceipt where",
                "",
                "canonicalYMSprint91WC3NewMathReceipt = Set",
                "",
                "-- T1",
                "t1CauchySchwarzContractionClosedConditionally = Set",
                "",
                "-- T2",
                "t2MasterConditionOpen = Set",
                "masterConditionOpen = Set",
                "",
                "-- T3",
                "t3WC3DerivedFalse = Set",
                "wc3DerivedFalse = Set",
                "",
                "-- T4",
                "t4ClayPromotedFalse = Set",
                "clayPromotedFalse = Set",
                "",
                "-- T5",
                "t5TheoremListT1ToT5Present = Set",
                "theoremListT1ToT5Present = Set",
            ]
        )
        + "\n"
    )


def test_sprint91_outputs_and_schema_for_missing_future_receipt(tmp_path: Path) -> None:
    repo_root = tmp_path / "empty_repo"
    repo_root.mkdir()
    out_dir, summary = run_audit(tmp_path, repo_root)

    assert summary["contract"] == "ym_sprint91_wc3_new_math_audit"
    assert (out_dir / "ym_sprint91_wc3_new_math_theorem_table.csv").exists()
    assert (out_dir / "ym_sprint91_wc3_new_math_gate_table.csv").exists()
    assert (out_dir / "ym_sprint91_wc3_new_math_summary.json").exists()
    assert summary["receipt_path"] == str(RECEIPT)
    assert summary["complete"] is False

    theorem_rows = read_csv(out_dir / "ym_sprint91_wc3_new_math_theorem_table.csv")
    gate_rows = read_csv(out_dir / "ym_sprint91_wc3_new_math_gate_table.csv")

    assert {row["theorem_id"] for row in theorem_rows} == {
        "T1",
        "T2",
        "T3",
        "T4",
        "T5",
    }
    assert {row["gate_name"] for row in gate_rows} >= {
        "T1CauchySchwarzContractionClosedConditionally",
        "MasterConditionOpen",
        "WC3DerivedFalse",
        "ClayPromotedFalse",
        "TheoremListT1ToT5Present",
    }


def test_sprint91_missing_future_receipt_fails_closed(tmp_path: Path) -> None:
    repo_root = tmp_path / "empty_repo"
    repo_root.mkdir()
    out_dir, summary = run_audit(tmp_path, repo_root)
    theorem_rows = read_csv(out_dir / "ym_sprint91_wc3_new_math_theorem_table.csv")

    assert summary["receipt_present"] is False
    assert summary["route_decision"] == "YM_SPRINT91_WC3_NEW_MATH_RECEIPT_MISSING"
    assert summary["t1_cauchy_schwarz_contraction_closed_conditionally"] is False
    assert summary["master_condition_open"] is False
    assert summary["wc3_derived"] is False
    assert summary["wc3_derived_false"] is False
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is False
    assert summary["theorem_list_t1_to_t5_present"] is False
    assert all(row["present_in_receipt"] == "False" for row in theorem_rows)


def test_sprint91_synthetic_receipt_records_expected_wc3_state(tmp_path: Path) -> None:
    repo_root = tmp_path / "repo"
    write_synthetic_receipt(repo_root)
    out_dir, summary = run_audit(tmp_path, repo_root)

    assert summary["receipt_present"] is True
    assert summary["route_decision"] == "YM_SPRINT91_WC3_NEW_MATH_OPEN_FAIL_CLOSED"
    assert summary["t1_cauchy_schwarz_contraction_closed_conditionally"] is True
    assert summary["master_condition_open"] is True
    assert summary["wc3_derived"] is False
    assert summary["wc3_derived_false"] is True
    assert summary["clay_yang_mills_promoted"] is False
    assert summary["clay_promotion_recorded_false"] is True
    assert summary["theorem_list_t1_to_t5_present"] is True
    assert summary["expected_theorem_ids"] == ["T1", "T2", "T3", "T4", "T5"]

    theorem_rows = read_csv(out_dir / "ym_sprint91_wc3_new_math_theorem_table.csv")
    assert all(row["present_in_receipt"] == "True" for row in theorem_rows)


def test_sprint91_gate_rows_report_stable_expected_fields(tmp_path: Path) -> None:
    repo_root = tmp_path / "repo"
    write_synthetic_receipt(repo_root)
    out_dir, _summary = run_audit(tmp_path, repo_root)
    gate_rows = read_csv(out_dir / "ym_sprint91_wc3_new_math_gate_table.csv")
    gates_by_name = {row["gate_name"]: row for row in gate_rows}

    assert gates_by_name["T1CauchySchwarzContractionClosedConditionally"][
        "required_anchor"
    ] == "t1CauchySchwarzContractionClosedConditionally"
    assert gates_by_name["MasterConditionOpen"]["actual_value"] == "True"
    assert gates_by_name["WC3DerivedFalse"]["actual_value"] == "True"
    assert gates_by_name["ClayPromotedFalse"]["actual_value"] == "True"
    assert gates_by_name["TheoremListT1ToT5Present"]["actual_value"] == "True"
