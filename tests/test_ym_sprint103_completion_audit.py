from __future__ import annotations

import json
import subprocess
import textwrap
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint103_completion_audit.py"
SUMMARY_NAME = "ym_sprint103_completion_summary.json"


ITEM_ANCHORS = [
    "BalabanCMP98LocalOscillationBound",
    "BalabanCMP98AveragingKernelIsProbability",
    "BalabanCMP116PolymerMassBound",
    "GaugeCovariantDobrushinComparison",
    "UniformPolymerActivityFromDobrushin",
    "WC3UniformClusterSummability",
    "ContinuumLimitMassGap",
    "Nontrivial4DSU3YangMillsMeasure",
]


def write_module(repo_root: Path, text: str) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True)
    (module_dir / "YMSprint103CompletionReceipt.agda").write_text(text)


def run_script(repo_root: Path, out_dir: Path) -> dict:
    subprocess.run(
        [
            "python",
            str(SCRIPT),
            "--repo-root",
            str(repo_root),
            "--out-dir",
            str(out_dir),
        ],
        cwd=REPO_ROOT,
        check=True,
    )
    return json.loads((out_dir / SUMMARY_NAME).read_text())


def sprint103_complete_module() -> str:
    anchors = "\n".join(f'        "{anchor}"' for anchor in ITEM_ANCHORS)
    return textwrap.dedent(
        f"""\
        module DASHI.Physics.Closure.YMSprint103CompletionReceipt where

        open import Agda.Builtin.Bool using (Bool; false; true)
        open import Agda.Builtin.Equality using (_≡_; refl)
        open import Agda.Builtin.String using (String)

        clayYangMillsPromoted : Bool
        clayYangMillsPromoted = false

        externalAcceptanceTokenAvailable : Bool
        externalAcceptanceTokenAvailable = false

        record YMSprint103CompletionReceipt : Set where
          field
            itemOne : String
            itemTwo : String
            itemThree : String
            itemFour : String
            itemFive : String
            itemSix : String
            itemSeven : String
            itemEight : String
            noClayPromotion : clayYangMillsPromoted ≡ false
            externalAcceptanceUnavailable :
              externalAcceptanceTokenAvailable ≡ false

        canonicalYMSprint103CompletionReceipt :
          YMSprint103CompletionReceipt
        canonicalYMSprint103CompletionReceipt =
          record
            {{ itemOne =
        {anchors}
            ; itemTwo =
                "BalabanCMP98AveragingKernelIsProbability"
            ; itemThree =
                "BalabanCMP116PolymerMassBound"
            ; itemFour =
                "GaugeCovariantDobrushinComparison"
            ; itemFive =
                "UniformPolymerActivityFromDobrushin"
            ; itemSix =
                "WC3UniformClusterSummability"
            ; itemSeven =
                "ContinuumLimitMassGap"
            ; itemEight =
                "Nontrivial4DSU3YangMillsMeasure"
            ; noClayPromotion =
                refl
            ; externalAcceptanceUnavailable =
                refl
            }}
        """
    )


def test_sprint103_completion_audit_accepts_all_eight_formal_receipts(
    tmp_path: Path,
) -> None:
    write_module(tmp_path, sprint103_complete_module())
    summary = run_script(tmp_path, tmp_path / "out")

    assert summary["sprint"] == "103-completion"
    assert summary["sprint103_module_count"] == 1
    assert summary["expected_math_item_count"] == 8
    assert summary["formal_receipt_completed_count"] == 8
    assert summary["all_eight_user_supplied_math_items_formally_receipted"] is True
    assert all(item["formal_receipt_completed"] for item in summary["math_items"])
    assert summary["formal_receipt_completion"]["complete"] is True
    assert summary["clayYangMillsPromoted"] is False
    assert summary["clay_promotion"]["no_clay_promotion"] is True


def test_sprint103_distinguishes_receipt_completion_from_external_acceptance(
    tmp_path: Path,
) -> None:
    write_module(tmp_path, sprint103_complete_module())
    summary = run_script(tmp_path, tmp_path / "out")

    assert (
        summary["external_acceptance"][
            "distinguished_from_formal_receipt_completion"
        ]
        is True
    )
    assert (
        summary["external_acceptance"][
            "external_acceptance_token_available_in_repo"
        ]
        is False
    )
    assert summary["external_acceptance"]["self_issuable_by_repo"] is False
    assert (
        summary["route_decision"]
        == "SPRINT103_FORMAL_RECEIPTS_COMPLETE_NO_EXTERNAL_ACCEPTANCE_NO_CLAY_PROMOTION"
    )


def test_sprint103_audit_fails_closed_for_missing_item_and_clay_promotion(
    tmp_path: Path,
) -> None:
    module = sprint103_complete_module()
    module = module.replace(
        "Nontrivial4DSU3YangMillsMeasure",
        "MissingSU3Measure",
    )
    module = module.replace(
        "clayYangMillsPromoted = false",
        "clayYangMillsPromoted = true",
    )
    write_module(tmp_path, module)

    summary = run_script(tmp_path, tmp_path / "out")
    statuses = {item["anchor"]: item for item in summary["math_items"]}

    assert summary["all_eight_user_supplied_math_items_formally_receipted"] is False
    assert summary["formal_receipt_completed_count"] == 7
    assert (
        statuses["Nontrivial4DSU3YangMillsMeasure"][
            "formal_receipt_completed"
        ]
        is False
    )
    assert summary["clayYangMillsPromoted"] is True
    assert summary["clay_promotion"]["no_clay_promotion"] is False
    assert summary["route_decision"] == "SPRINT103_AUDIT_FAIL_CLOSED"
