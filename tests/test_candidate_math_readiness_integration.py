from __future__ import annotations

import importlib.util
import json
import shutil
import subprocess
import sys
from pathlib import Path
from types import ModuleType
from typing import Any, Iterable

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]

CANDIDATE_MATH_SCRIPTS = (
    REPO_ROOT / "scripts" / "ns_missing_math_theorem_agenda.py",
    REPO_ROOT / "scripts" / "ym_missing_math_theorem_agenda.py",
    REPO_ROOT / "scripts" / "uct_missing_math_theorem_agenda.py",
    REPO_ROOT / "scripts" / "full_missing_math_theorem_agenda.py",
)

CANDIDATE_AUDIT_SCRIPTS = (
    REPO_ROOT / "scripts" / "ns_stationarity_candidate_audit.py",
    REPO_ROOT / "scripts" / "ns_kappa_bias_candidate_audit.py",
    REPO_ROOT / "scripts" / "ym_finite_domination_candidate_audit.py",
    REPO_ROOT / "scripts" / "clay_submission_evidence_matrix.py",
)

CANDIDATE_MATH_RECEIPTS = (
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "FullMissingMathTheoremAgendaBoundary.agda",
    REPO_ROOT
    / "DASHI"
    / "Physics"
    / "Closure"
    / "ClaySubmissionCandidateMathBoundary.agda",
)


def load_script(name: str) -> ModuleType:
    path = REPO_ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def walk(value: Any) -> Iterable[Any]:
    yield value
    if isinstance(value, dict):
        for item in value.values():
            yield from walk(item)
    elif isinstance(value, list):
        for item in value:
            yield from walk(item)


def run_json_script(path: Path) -> dict[str, Any]:
    result = subprocess.run(
        [sys.executable, str(path), "--format", "json"],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    payload = json.loads(result.stdout)
    assert isinstance(payload, dict), path
    return payload


def run_candidate_audit(path: Path, tmp_path: Path) -> dict[str, Any]:
    if path.name == "ym_finite_domination_candidate_audit.py":
        out_dir = tmp_path / "ym-finite-domination"
        result = subprocess.run(
            [
                sys.executable,
                str(path),
                "--repo-root",
                str(REPO_ROOT),
                "--out-dir",
                str(out_dir),
                "--no-markdown",
            ],
            cwd=REPO_ROOT,
            text=True,
            capture_output=True,
            check=False,
        )
        assert result.returncode in (0, 1), result.stderr or result.stdout
        assert "fail-closed" in (result.stdout + result.stderr).lower()
        summary = out_dir / "ym_finite_domination_candidate_audit_summary.json"
        assert summary.exists(), result.stdout + result.stderr
        payload = json.loads(summary.read_text(encoding="utf-8"))
        assert isinstance(payload, dict), path
        return payload

    command = [sys.executable, str(path)]
    if path.name in {
        "ns_stationarity_candidate_audit.py",
        "clay_submission_evidence_matrix.py",
    }:
        command.extend(["--format", "json"])

    result = subprocess.run(
        command,
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stderr or result.stdout
    payload = json.loads(result.stdout)
    assert isinstance(payload, dict), path
    return payload


def positive_promotion_fields(payload: Any) -> list[str]:
    bad: list[str] = []
    for value in walk(payload):
        if not isinstance(value, dict):
            continue
        for key, item in value.items():
            key_lower = key.lower()
            if "promotion" not in key_lower and "promoted" not in key_lower:
                continue
            if key_lower.startswith(("no_", "non_", "never_", "not_")):
                continue
            if "false" in key_lower or "fail_closed" in key_lower or "guard" in key_lower:
                continue
            if item is True:
                bad.append(f"{key}=true")
            if isinstance(item, str) and item.lower() in {"true", "promoted", "allowed"}:
                bad.append(f"{key}={item}")
    return bad


def test_candidate_math_scripts_exist_run_and_stay_non_promoting() -> None:
    missing = [str(path.relative_to(REPO_ROOT)) for path in CANDIDATE_MATH_SCRIPTS if not path.exists()]
    assert missing == []

    for script in CANDIDATE_MATH_SCRIPTS:
        payload = run_json_script(script)
        assert payload.get("ok", True) is True, script.name
        assert payload.get("fail_closed") is True, script.name
        assert positive_promotion_fields(payload) == [], script.name


def test_candidate_audit_scripts_exist_run_and_stay_non_promoting(tmp_path: Path) -> None:
    missing = [str(path.relative_to(REPO_ROOT)) for path in CANDIDATE_AUDIT_SCRIPTS if not path.exists()]
    assert missing == []

    for script in CANDIDATE_AUDIT_SCRIPTS:
        payload = run_candidate_audit(script, tmp_path)
        assert positive_promotion_fields(payload) == [], script.name
        assert payload.get("fail_closed", True) is True or "fail-closed" in json.dumps(payload).lower()
        assert not payload.get("clay_eligible_proof", False), script.name


def test_candidate_math_readiness_checker_tracks_scripts_and_receipt() -> None:
    readiness = load_script("check_publication_readiness")

    results = readiness.check_theorem_agenda_surfaces(REPO_ROOT)
    failures = {result.name: result.detail for result in results if not result.ok}
    assert failures == {}

    script_paths = {script["path"].as_posix() for script in readiness.THEOREM_AGENDA_SCRIPTS}
    assert {path.relative_to(REPO_ROOT).as_posix() for path in CANDIDATE_MATH_SCRIPTS} <= script_paths

    receipt_paths = {receipt["path"].as_posix() for receipt in readiness.THEOREM_AGENDA_RECEIPTS}
    for receipt in CANDIDATE_MATH_RECEIPTS:
        assert receipt.relative_to(REPO_ROOT).as_posix() in receipt_paths or receipt.exists()


def test_candidate_math_agda_receipt_exists_and_typechecks_fail_closed() -> None:
    candidate_receipt = CANDIDATE_MATH_RECEIPTS[0]
    assert candidate_receipt.exists()
    text = candidate_receipt.read_text(encoding="utf-8")

    for term in (
        "canonicalFullMissingMathTheoremAgendaBoundary",
        "fullAgendaFailClosedIsTrue",
        "allPromotionFlagsFalse",
        "promotionAllowedIsFalse",
        "clayPromotionIsFalse",
        "terminalPromotionIsFalse",
    ):
        assert term in text

    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(candidate_receipt.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr


def test_clay_submission_candidate_math_receipt_exists_and_typechecks_fail_closed() -> None:
    receipt = CANDIDATE_MATH_RECEIPTS[1]
    assert receipt.exists()
    text = receipt.read_text(encoding="utf-8")

    for term in (
        "NSAStationarityCandidate",
        "NSCKappaBiasCandidate",
        "YMAFiniteDominationCandidate",
        "W_r energy ODE",
        "OU bias balance",
        "Bochner-Weitzenbock domination",
        "candidateMathBoundaryProofPromotedIsFalse",
        "candidateMathBoundaryClayEligibleIsFalse",
    ):
        assert term in text

    agda = shutil.which("agda")
    if agda is None:
        pytest.skip("agda executable is not available")

    result = subprocess.run(
        [agda, "--no-libraries", str(receipt.relative_to(REPO_ROOT))],
        cwd=REPO_ROOT,
        text=True,
        capture_output=True,
        check=False,
    )
    assert result.returncode == 0, result.stdout + result.stderr
