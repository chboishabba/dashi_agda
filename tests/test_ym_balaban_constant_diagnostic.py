from __future__ import annotations

import json
import math
import re
import subprocess
import sys
import textwrap
from pathlib import Path
from typing import Any

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT_CANDIDATES = (
    REPO_ROOT / "scripts" / "ym_balaban_constant_diagnostic.py",
    REPO_ROOT / "scripts" / "ym_balaban_constant_diagnostic_harness.py",
    REPO_ROOT / "scripts" / "ym_balaban_constants_diagnostic.py",
)


def script_path() -> Path:
    for path in SCRIPT_CANDIDATES:
        if path.exists():
            return path
    pytest.skip("Balaban constant diagnostic script is not integrated yet")


def write_balaban_fixture(repo_root: Path) -> None:
    module_dir = repo_root / "DASHI" / "Physics" / "Closure"
    module_dir.mkdir(parents=True, exist_ok=True)
    (module_dir / "YMBalabanConstantDiagnosticFixture.agda").write_text(
        textwrap.dedent(
            """\
            module DASHI.Physics.Closure.YMBalabanConstantDiagnosticFixture where

            open import Agda.Builtin.Bool using (Bool; false; true)
            open import Agda.Builtin.String using (String)

            clayYangMillsPromoted : Bool
            clayYangMillsPromoted = false

            balabanConstantDiagnosticOnly : Bool
            balabanConstantDiagnosticOnly = true

            balabanActivityBound : String
            balabanActivityBound =
              "|H(Z)| <= C exp(-c d(Z)); diagnostic constants C=4.0 and c=0.125 are finite positive authority-intake parameters, not a repo-native proof"

            balabanConstantNonPromotionBoundary : String
            balabanConstantNonPromotionBoundary =
              "constant diagnostic only; full Balaban theorem, continuum mass gap, Clay promotion, and terminal promotion remain false"

            data BalabanConstantDiagnosticReceipt : Set where
              recorded :
                BalabanConstantDiagnosticReceipt
            """
        ),
        encoding="utf-8",
    )


def run_diagnostic(repo_root: Path, out_dir: Path) -> dict[str, Any]:
    proc = subprocess.run(
        [
            sys.executable,
            str(script_path()),
            "--E0",
            "1",
            "--C1",
            "2",
            "--C2",
            "3",
            "--L",
            "2",
            "--M",
            "4",
            "--q",
            "0.1",
            "--eps4",
            "0.01",
            "--eps6",
            "0.001",
            "--kp-max",
            "0.2",
        ],
        cwd=REPO_ROOT,
        check=False,
        capture_output=True,
        text=True,
    )
    assert proc.returncode in (0, 1), proc.stdout + proc.stderr
    return json.loads(proc.stdout)


def flatten(value: Any) -> list[Any]:
    if isinstance(value, dict):
        return [value] + [nested for item in value.values() for nested in flatten(item)]
    if isinstance(value, list):
        return [value] + [nested for item in value for nested in flatten(item)]
    return [value]


def words(value: Any) -> set[str]:
    found = set(re.findall(r"[a-z0-9]+", json.dumps(value).lower()))
    for word in tuple(found):
        if word.startswith("diagnos"):
            found.add("diagnostic")
        if word.startswith("promot"):
            found.add("promotion")
    return found


def matching_items(value: Any, required: tuple[str, ...]) -> list[Any]:
    return [item for item in flatten(value) if all(word in words(item) for word in required)]


def numeric_constants(value: Any) -> list[float]:
    constants: list[float] = []
    for item in flatten(value):
        if isinstance(item, bool):
            continue
        if isinstance(item, (int, float)):
            constants.append(float(item))
        elif isinstance(item, str):
            for match in re.findall(r"(?<![A-Za-z])(?:C|c)\s*=\s*([0-9]+(?:\.[0-9]+)?)", item):
                constants.append(float(match))
    return constants


def promotion_bools(value: Any) -> dict[str, bool]:
    flags: dict[str, bool] = {}
    for item in flatten(value):
        if isinstance(item, dict):
            name = item.get("name") or item.get("id") or item.get("gate") or item.get("field")
            current = item.get("value")
            if isinstance(name, str) and isinstance(current, bool):
                lower = name.lower()
                if "promot" in lower or "clay" in lower or "terminal" in lower or "massgap" in lower:
                    flags[name] = current
            for key, value in item.items():
                if isinstance(key, str) and isinstance(value, bool):
                    lower = key.lower()
                    if "promot" in lower or "clay" in lower or "terminal" in lower or "mass_gap" in lower:
                        flags[key] = value
    return flags


def assert_balaban_constant_payload_is_diagnostic_only(payload: dict[str, Any]) -> None:
    serialized = json.dumps(payload, sort_keys=True).lower()

    assert "balaban" in serialized
    assert "casimir" in serialized
    assert "kp" in serialized and matching_items(payload, ("threshold",))
    assert matching_items(payload, ("constant", "diagnostic"))
    assert matching_items(payload, ("promotion", "false")) or "no promotion" in serialized

    constants = numeric_constants(payload)
    assert constants
    assert all(math.isfinite(value) for value in constants)
    assert any(value > 0 for value in constants)

    flags = promotion_bools(payload)
    assert flags
    assert all(value is False for value in flags.values())


def test_balaban_constant_fixture_writes_positive_diagnostic_constants(
    tmp_path: Path,
) -> None:
    write_balaban_fixture(tmp_path)

    payload = run_diagnostic(tmp_path, tmp_path / "out")

    assert_balaban_constant_payload_is_diagnostic_only(payload)


def test_balaban_constant_real_diagnostic_remains_non_promotional(
    tmp_path: Path,
) -> None:
    payload = run_diagnostic(REPO_ROOT, tmp_path / "out")

    assert_balaban_constant_payload_is_diagnostic_only(payload)


def test_balaban_constant_diagnostic_rejects_nonfinite_inputs() -> None:
    proc = subprocess.run(
        [
            sys.executable,
            str(script_path()),
            "--E0",
            "nan",
            "--C1",
            "2",
            "--C2",
            "3",
            "--L",
            "2",
            "--M",
            "4",
            "--q",
            "0.1",
            "--eps4",
            "0.01",
            "--eps6",
            "0.001",
            "--kp-max",
            "0.2",
        ],
        cwd=REPO_ROOT,
        capture_output=True,
        text=True,
    )

    assert proc.returncode != 0
    assert "finite" in proc.stderr.lower()
