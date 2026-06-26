from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
CLOSURE = REPO_ROOT / "DASHI" / "Physics" / "Closure"
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"
AUDIT_SCRIPT = REPO_ROOT / "scripts" / "perelman_bt_geometry_boundary_audit.py"

MODULES = {
    "DASHI.Physics.Closure.BTBallVolumeEntropyBoundary": {
        "path": CLOSURE / "BTBallVolumeEntropyBoundary.agda",
        "identifiers": (
            "BTBallVolumeEntropyBoundary",
            "canonicalBTBallVolumeEntropyBoundary",
            "regularTreeBallFormulaText",
            "productBallFormulaText",
            "productAsymptoticFormulaText",
            "entropyLabelText",
            "canonicalEntropyLog42Recorded",
        ),
        "boundary_terms": (
            "bruhat",
            "tits",
            "ball",
            "volume",
            "entropy",
            "product",
            "false",
        ),
    },
    "DASHI.Physics.Closure.BTGaussianReducedVolumeBoundary": {
        "path": CLOSURE / "BTGaussianReducedVolumeBoundary.agda",
        "identifiers": (
            "BTGaussianReducedVolumeBoundary",
            "canonicalBTGaussianReducedVolumeBoundary",
            "gaussianReducedVolumeSeries",
            "convergenceFlagIsTrue",
            "monotonicityTheoremFlagIsFalse",
            "SmoothPerelmanMonotonicityTheoremPromoted",
            "canonicalMonotonicityFlagFalse",
        ),
        "boundary_terms": (
            "perelman",
            "gaussian",
            "reduced-volume",
            "convergence",
            "monotonicity",
            "bruhat",
            "tits",
            "false",
        ),
    },
    "DASHI.Physics.Closure.BTNeckJSJGeometryAnalogueBoundary": {
        "path": CLOSURE / "BTNeckJSJGeometryAnalogueBoundary.agda",
        "identifiers": (
            "BTNeckJSJGeometryAnalogueBoundary",
            "canonicalBTNeckJSJGeometryAnalogueBoundary",
            "BTNeckAnalogue",
            "JSJAnalogue",
            "GeometryAnalogue",
            "geometrizationProvedHereIsFalse",
            "boundaryGeometrizationBlocked",
        ),
        "boundary_terms": (
            "neck",
            "jsj",
            "geometry",
            "analogue",
            "bruhat",
            "tits",
            "false",
        ),
    },
    "DASHI.Physics.Closure.PerelmanRicciFlowAndGeometrizationBoundaryReceipt": {
        "path": CLOSURE / "PerelmanRicciFlowAndGeometrizationBoundaryReceipt.agda",
        "identifiers": (
            "PerelmanRicciFlowAndGeometrizationBoundaryReceipt",
            "canonicalPerelmanRicciFlowAndGeometrizationBoundaryReceipt",
            "AuthoritySocket",
            "authorityAvailableIsFalse",
            "smoothRicciFlowExistenceUniquenessSocket",
            "reducedVolumeMonotonicitySocket",
            "thurstonGeometrizationSocket",
            "allPerelmanBoundaryAuthoritySocketsClosed",
            "thurstonGeometrizationAuthorityNotPromoted",
        ),
        "boundary_terms": (
            "perelman",
            "ricci-flow",
            "geometrization",
            "authority",
            "socket",
            "false",
        ),
    },
}

FORBIDDEN_PATTERNS = {
    "postulate": re.compile(r"(?<![A-Za-z0-9_])postulate(?![A-Za-z0-9_])"),
    "Agda hole": re.compile(re.escape("{" + "!") + r"|" + re.escape("!" + "}")),
    "rhs meta": re.compile(r"(?m)^\s*[A-Za-z][A-Za-z0-9'_]*\s*(?::[^=\n]+)?=\s*\?\s*$"),
}


def _read_module_texts() -> dict[str, str]:
    texts: dict[str, str] = {}
    missing: list[str] = []
    for module_name, spec in MODULES.items():
        path = spec["path"]
        actual_module = str(spec.get("module", module_name))
        if not path.is_file():
            missing.append(f"{actual_module}: {path.relative_to(REPO_ROOT)}")
            continue
        texts[actual_module] = path.read_text(encoding="utf-8")

    assert not missing, "missing expected Perelman/BT Agda modules:\n" + "\n".join(
        missing
    )
    return texts


def _audit_check_rows(payload: object) -> list[dict[str, object]]:
    if not isinstance(payload, dict):
        return []

    checks = payload.get("checks")
    if isinstance(checks, list):
        return [row for row in checks if isinstance(row, dict)]
    if isinstance(checks, dict):
        rows: list[dict[str, object]] = []
        for name, value in checks.items():
            if isinstance(value, dict):
                row = {"name": name}
                row.update(value)
                rows.append(row)
            else:
                rows.append({"name": name, "passed": value})
        return rows

    required = payload.get("required_checks")
    if isinstance(required, dict):
        return [{"name": name, "passed": value} for name, value in required.items()]
    return []


def _row_passed(row: dict[str, object]) -> bool | None:
    for key in ("passed", "pass", "ok", "status"):
        value = row.get(key)
        if isinstance(value, bool):
            return value
        if isinstance(value, str):
            lowered = value.lower()
            if lowered in {"pass", "passed", "ok", "true"}:
                return True
            if lowered in {"fail", "failed", "false"}:
                return False
            if lowered in {"pending", "skip", "skipped"}:
                return None
    return None


def test_perelman_bt_geometry_modules_exist_and_have_no_postulates_or_holes() -> None:
    for module_name, text in _read_module_texts().items():
        assert f"module {module_name} where" in text
        for label, pattern in FORBIDDEN_PATTERNS.items():
            assert not pattern.search(text), f"{module_name} contains {label}"


def test_perelman_bt_geometry_modules_record_required_identifiers() -> None:
    module_texts = _read_module_texts()
    for module_name, spec in MODULES.items():
        actual_module = str(spec.get("module", module_name))
        text = module_texts[actual_module]
        for identifier in spec["identifiers"]:
            assert identifier in text, f"{actual_module} missing {identifier}"


def test_perelman_bt_geometry_boundary_language_is_fail_closed() -> None:
    module_texts = _read_module_texts()
    combined = "\n".join(module_texts.values()).lower()
    assert "true" in combined
    assert "false" in combined
    assert "perelman" in combined
    assert "bruhat" in combined and "tits" in combined
    assert "promot" in combined

    for module_name, spec in MODULES.items():
        actual_module = str(spec.get("module", module_name))
        lowered = module_texts[actual_module].lower()
        for term in spec["boundary_terms"]:
            assert term in lowered, f"{actual_module} missing boundary term {term!r}"


def test_perelman_bt_geometry_audit_json_passes_non_aggregate_checks() -> None:
    assert AUDIT_SCRIPT.is_file(), (
        "missing Perelman/BT geometry boundary audit script: "
        f"{AUDIT_SCRIPT.relative_to(REPO_ROOT)}"
    )

    result = subprocess.run(
        [
            "python",
            str(AUDIT_SCRIPT.relative_to(REPO_ROOT)),
            "--allow-missing-aggregate",
        ],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr

    payload = json.loads(result.stdout)
    encoded = json.dumps(payload)
    for module_name, spec in MODULES.items():
        actual_module = str(spec.get("module", module_name))
        assert actual_module.rsplit(".", maxsplit=1)[-1] in encoded

    rows = _audit_check_rows(payload)
    assert rows, "audit JSON did not expose check rows"
    for row in rows:
        name = str(row.get("name", "")).lower()
        if "aggregate" in name:
            continue
        assert _row_passed(row) is True, row


def test_perelman_bt_geometry_modules_imported_by_everything_when_integrated() -> None:
    assert EVERYTHING.is_file(), "missing DASHI/Everything.agda"
    text = EVERYTHING.read_text(encoding="utf-8")
    missing = [
        str(spec.get("module", module_name))
        for module_name, spec in MODULES.items()
        if f"import {spec.get('module', module_name)}" not in text
    ]
    assert not missing, "DASHI/Everything.agda is missing imports:\n" + "\n".join(
        missing
    )
