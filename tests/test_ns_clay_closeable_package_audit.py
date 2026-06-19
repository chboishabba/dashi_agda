from __future__ import annotations

import importlib.util
import json
import subprocess
import sys
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ns_clay_closeable_package_audit.py"


def load_module():
    spec = importlib.util.spec_from_file_location("ns_clay_closeable_package_audit", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def run_script(tmp_path: Path) -> dict[str, object]:
    output = tmp_path / "ns_clay_closeable_package_audit.json"
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--output", str(output)],
        cwd=REPO_ROOT,
        check=False,
        text=True,
        capture_output=True,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    payload = json.loads(result.stdout)
    file_payload = json.loads(output.read_text(encoding="utf-8"))
    assert payload == file_payload
    return payload


def test_ns_clay_closeable_package_audit_emits_exact_surface(tmp_path: Path) -> None:
    payload = run_script(tmp_path)

    assert payload["contract"] == "ns_clay_closeable_package_audit"
    assert payload["version"] == 1
    assert payload["validation_passed"] is True

    assert payload["closeable_package_count"] == 7
    assert payload["closeable_package_names"] == [
        "millerToH5",
        "GD3 two-gap",
        "coareaGradientBound",
        "LocalConcentration",
        "pigeon_concentration",
        "StepA_PerComponent",
        "BoundaryHB_Correct",
    ]
    assert [item["package_name"] for item in payload["closeable_packages"]] == payload[
        "closeable_package_names"
    ]
    assert all(item["target_receipt_exists"] is True for item in payload["closeable_packages"])

    assert [item["target_receipt_ref"] for item in payload["closeable_packages"]] == [
        "DASHI/Physics/Closure/NSKatoHessianConfinementReceipt.agda",
        "DASHI/Physics/Closure/NSKatoHessianConfinementReceipt.agda",
        "DASHI/Physics/Closure/NSCoareaGradientStepAPerComponentReceipt.agda",
        "DASHI/Physics/Closure/LocalConcentrationPigeonConcentrationReceipt.agda",
        "DASHI/Physics/Closure/LocalConcentrationPigeonConcentrationReceipt.agda",
        "DASHI/Physics/Closure/NSCoareaGradientStepAPerComponentReceipt.agda",
        "DASHI/Physics/Closure/Lambda2PlusTransportInequalityBoundaryHBReceipt.agda",
    ]

    assert payload["hard_walls"] == ["KornLevelSet", "collapseImpossible"]
    assert payload["hard_wall_count"] == 2
    assert payload["hard_wall_receipt_ref"] == (
        "DASHI/Physics/Closure/NSHardTheoremKornCollapseWallPostCalc11Receipt.agda"
    )
    assert payload["hard_wall_receipt_exists"] is True
    assert payload["clay_hard_core"] == "collapseImpossible"

    assert payload["promotion"] is False
    assert payload["theorem_promotion"] is False
    assert payload["clay_promotion"] is False
    assert payload["promotion_flags"] == {
        "promotion_allowed": False,
        "promotion_blocked": True,
        "theorem_promotion": False,
        "clay_promotion": False,
    }

    assert set(payload["control_card"]) == {"O", "R", "C", "S", "L", "P", "G", "F"}
    assert "fail-closed" in payload["control_card"]["R"]


def test_ns_clay_closeable_package_audit_validator_rejects_tampering() -> None:
    module = load_module()
    payload = module.build_payload()
    assert module.validate_payload(payload) is True

    tampered = json.loads(json.dumps(payload))
    tampered["closeable_packages"][0]["package_name"] = "wrong"
    assert module.validate_payload(tampered) is False

    tampered_hard_wall = json.loads(json.dumps(payload))
    tampered_hard_wall["hard_walls"] = ["KornLevelSet"]
    assert module.validate_payload(tampered_hard_wall) is False

    tampered_promotion = json.loads(json.dumps(payload))
    tampered_promotion["promotion"] = True
    assert module.validate_payload(tampered_promotion) is False
