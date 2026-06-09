from __future__ import annotations

import json
import re
import shutil
import subprocess
import sys
from collections.abc import Iterable
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
STEM = "ns_sprint153_source_dissipation_balance"
SCRIPT = REPO_ROOT / "scripts" / f"{STEM}.py"
OUTPUT_DIR = REPO_ROOT / "outputs" / STEM
SUMMARY = OUTPUT_DIR / f"{STEM}_summary.json"
RECEIPT = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "NSSprint153LocalizedVortexStretchingSourceReceipt.agda"
)

CONTROL_CARD_KEYS = {"O", "R", "C", "S", "L", "P", "G", "F"}
FALSE_SUMMARY_FLAGS = {
    "localized_vortex_stretching_source_model_valid",
    "source_dissipation_balance_proved",
    "model_validity_for_width_ode",
    "model_validity_closed",
    "symmetric_hou_luo_bkm_finite",
    "bkm_finite",
    "bkm_guard_closed",
    "full_clay_ns_solved",
    "clay_navier_stokes_promoted",
    "promotion_allowed",
    "claim_closed",
    "claim_proved",
    "claim_proven",
}
AGDA_FALSE_ASSIGNMENTS = {
    "LocalizedVortexStretchingSourceBound",
    "LocalizedVortexStretchingSourceBoundProved",
    "localizedVortexStretchingSourceBound",
    "localizedVortexStretchingSourceBoundProved",
    "BiotSavartNonlocalClosureAtScaleDelta",
    "BiotSavartNonlocalClosureAtScaleDeltaProved",
    "SimultaneousConstantsCompatibility",
    "SimultaneousConstantsCompatibilityProved",
    "ModelValidityForWidthODE",
    "ModelValidityForWidthODEProved",
    "SymmetricHouLuoBKMFinite",
    "SymmetricHouLuoBKMFiniteProved",
    "fullClayNSSolved",
    "full_clay_ns_solved",
    "clayNavierStokesPromoted",
}
TRUE_CLOSURE_PATTERNS = (
    re.compile(
        r'"(?:localized_vortex_stretching_source_model_valid|'
        r'source_dissipation_balance_proved|model_validity_for_width_ode|'
        r'symmetric_hou_luo_bkm_finite|bkm_finite|full_clay_ns_solved|'
        r'clay_navier_stokes_promoted|promotion_allowed)"\s*:\s*true\b',
        re.IGNORECASE,
    ),
    re.compile(
        r"\b(?:LocalizedVortexStretchingSourceModelValid|"
        r"LocalizedVortexStretchingSourceModelValidProved|"
        r"SourceDissipationBalanceAtScaleDelta|"
        r"SourceDissipationBalanceAtScaleDeltaProved|"
        r"ModelValidityForWidthODE|ModelValidityForWidthODEProved|"
        r"SymmetricHouLuoBKMFinite|SymmetricHouLuoBKMFiniteProved|"
        r"full_clay_ns_solved|clayNavierStokesPromoted|promotionAllowed)"
        r"\s*=\s*true\b"
    ),
)


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for child in value.values():
            yield from walk(child)
    elif isinstance(value, list):
        for child in value:
            yield from walk(child)


def normalize(value: Any) -> str:
    return re.sub(r"[^a-z0-9]+", "_", str(value).lower()).strip("_")


def as_bool(value: Any) -> bool | None:
    if isinstance(value, bool):
        return value
    if isinstance(value, str) and value.lower() in {"true", "false"}:
        return value.lower() == "true"
    return None


def bool_values_for_keys(payload: Any, *names: str) -> list[bool]:
    wanted = {normalize(name) for name in names}
    found: list[bool] = []
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        for key, value in item.items():
            if normalize(key) in wanted:
                parsed = as_bool(value)
                if parsed is not None:
                    found.append(parsed)
    return found


def compact(value: Any) -> str:
    return normalize(json.dumps(value, sort_keys=True, default=str))


def agda_bool_assignment(text: str, name: str, value: bool) -> bool:
    expected = "true" if value else "false"
    return re.search(rf"\b{re.escape(name)}\s*=\s*{expected}\b", text) is not None


def load_balance_summary(tmp_path: Path) -> tuple[dict[str, Any], str]:
    if SCRIPT.is_file():
        out_dir = tmp_path / STEM
        result = subprocess.run(
            [
                sys.executable,
                str(SCRIPT),
                "--repo-root",
                str(REPO_ROOT),
                "--out-dir",
                str(out_dir),
            ],
            cwd=REPO_ROOT,
            check=False,
            text=True,
            capture_output=True,
        )
        artifacts = sorted(out_dir.glob("*")) if out_dir.exists() else []
        artifact_text = "\n".join(
            path.read_text(encoding="utf-8", errors="replace")
            for path in artifacts
            if path.suffix.lower() in {".json", ".csv", ".md"}
        )
        combined = "\n".join([result.stdout, result.stderr, artifact_text])
        assert result.returncode == 0, combined
        summaries = sorted(out_dir.glob("*_summary.json"))
        assert summaries, combined
        summary = json.loads(summaries[0].read_text(encoding="utf-8"))
        return summary, "\n".join([combined, compact(summary)])

    assert SUMMARY.is_file(), (
        f"missing Sprint153 summary and emitter: {SUMMARY.relative_to(REPO_ROOT)}, "
        f"{SCRIPT.relative_to(REPO_ROOT)}"
    )
    summary = json.loads(SUMMARY.read_text(encoding="utf-8"))
    return summary, compact(summary)


def assert_control_card(payload: dict[str, Any], text: str) -> None:
    for item in walk(payload):
        if not isinstance(item, dict):
            continue
        card = item.get("control_card") or item.get("control-card")
        if isinstance(card, dict) and CONTROL_CARD_KEYS.issubset({str(key) for key in card}):
            return
        if CONTROL_CARD_KEYS.issubset({str(key) for key in item}):
            return
    missing = [key for key in CONTROL_CARD_KEYS if normalize(key) not in normalize(text)]
    assert not missing, f"missing control-card keys {missing}\n{text}"


def test_sprint153_agda_receipt_exists_records_source_surface_and_typechecks() -> None:
    assert RECEIPT.is_file(), f"missing receipt: {RECEIPT.relative_to(REPO_ROOT)}"
    text = RECEIPT.read_text(encoding="utf-8")
    normalized = normalize(text)

    required_terms = {
        "NSSprint153LocalizedVortexStretchingSourceReceipt",
        "LocalizedVortexStretchingSource",
        "LocalizedVortexStretchingSourceBound",
        "Sprint152AnnularLeakageDominationSupport",
        "Sprint152AnnularLeakageDominationConditional",
        "vortexStretchingSource",
        "annularLeakage",
        "NSSprint151LocalizedEnstrophyIdentityReceipt",
        "fail",
        "closed",
    }
    missing_terms = [term for term in required_terms if normalize(term) not in normalized]
    assert not missing_terms, missing_terms

    assert agda_bool_assignment(text, "Sprint152AnnularLeakageDominationSupport", True)
    assert agda_bool_assignment(text, "Sprint152AnnularLeakageDominationConditional", True)
    assert agda_bool_assignment(text, "Sprint152AnnularLeakageDominationTheorem", False)
    for name in AGDA_FALSE_ASSIGNMENTS:
        assert agda_bool_assignment(text, name, False), name
    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern

    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")
    result = subprocess.run(
        [agda, str(RECEIPT.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_sprint153_source_dissipation_summary_keeps_leakage_support_fail_closed(
    tmp_path: Path,
) -> None:
    summary, text = load_balance_summary(tmp_path)
    normalized = compact(summary)

    assert_control_card(summary, text)
    assert "bounded_leakage" in normalized
    assert "sprint152_bounded_leakage_residual" in normalized
    assert "source" in normalized
    assert "dissipation" in normalized
    assert "model" in normalized
    assert "bkm" in normalized
    assert "clay" in normalized

    observed_row_ids = {normalize(row_id) for row_id in summary.get("observed_row_ids", [])}
    open_or_residual_rows = {
        normalize(row_id) for row_id in summary.get("open_or_residual_rows", [])
    }
    assert "sprint152_bounded_leakage_residual" in observed_row_ids
    assert "sprint152_bounded_leakage_residual" in open_or_residual_rows
    assert str(summary.get("sprint152_bounded_leakage_residual", "")).strip()

    for name in FALSE_SUMMARY_FLAGS:
        values = bool_values_for_keys(summary, name)
        if values:
            assert all(value is False for value in values), (name, values)
    assert any(
        bool_values_for_keys(summary, name)
        for name in (
            "localized_vortex_stretching_source_model_valid",
            "model_validity_for_width_ode",
            "model_validity_closed",
        )
    ), f"missing false model-validity flag\n{text}"
    assert any(
        bool_values_for_keys(summary, name)
        for name in ("symmetric_hou_luo_bkm_finite", "bkm_finite", "bkm_guard_closed")
    ), f"missing false BKM flag\n{text}"
    assert any(
        bool_values_for_keys(summary, name)
        for name in ("full_clay_ns_solved", "clay_navier_stokes_promoted")
    ), f"missing false Clay flag\n{text}"

    for pattern in TRUE_CLOSURE_PATTERNS:
        assert not pattern.search(text), pattern.pattern
