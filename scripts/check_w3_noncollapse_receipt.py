#!/usr/bin/env python3
from __future__ import annotations

import argparse
import hashlib
import json
import math
import re
from pathlib import Path
from typing import Any


ROOT = Path(__file__).resolve().parents[1]
DEFAULT_COMPARISON_PATH = (
    ROOT / "logs/research/w3_frozen_3205d74_t43_comparison_20260513.json"
)
DEFAULT_AGDA_PATH = (
    ROOT / "DASHI/Physics/Closure/HEPDataW3NonCollapseWitnessReceipt.agda"
)
DEFAULT_PROVIDER_CHECKSUMS_PATH = (
    ROOT / "logs/research/provider_inputs/hepdata_ins2079374/checksums.txt"
)

EXPECTED_COMPARISON_SHA256 = (
    "92b61032c06cb4d00d22e00bf9e280b47806f9ebf18f012f5b82a41b0afae238"
)
EXPECTED_T43_CANONICAL_SHA256 = (
    "5cfefe5a5a99c415f9225a3515383e8ce5e9a874861ff6c5fc08365871bfd340"
)
EXPECTED_T44_CANONICAL_SHA256 = (
    "2dfa2abe120981f1f8379d95c8d6e0362394c6f6c8fed01dd45fc76a3e2b660b"
)

EXPECTED_WITNESS = {
    "binIndex": 12,
    "phiStar": 0.10250000000000001,
    "phiStarLow": 0.091,
    "phiStarHigh": 0.114,
    "prediction": 0.0486590199823977,
    "data": 0.049758,
    "covarianceSigma": 0.00048197510309143566,
    "pull": -2.280159308132989,
    "residual": -0.001098980017602294,
}


def sha256_file(path: Path) -> str:
    digest = hashlib.sha256()
    with path.open("rb") as handle:
        for chunk in iter(lambda: handle.read(1024 * 1024), b""):
            digest.update(chunk)
    return digest.hexdigest()


def _require(condition: bool, message: str) -> None:
    if not condition:
        raise ValueError(message)


def _require_close(actual: float, expected: float, label: str) -> None:
    _require(
        math.isclose(actual, expected, rel_tol=0.0, abs_tol=1e-12),
        f"{label} mismatch: expected {expected!r}, got {actual!r}",
    )


def _load_json(path: Path) -> dict[str, Any]:
    with path.open("r", encoding="utf-8") as handle:
        payload = json.load(handle)
    _require(isinstance(payload, dict), f"{path} must contain a JSON object")
    return payload


def _read_checksum_manifest(path: Path) -> dict[str, str]:
    checksums: dict[str, str] = {}
    for line in path.read_text(encoding="utf-8").splitlines():
        if not line.strip():
            continue
        checksum, relpath = line.split(maxsplit=1)
        checksums[relpath] = checksum
    return checksums


def _canonical_runner_record_body(agda_text: str) -> str:
    marker = "canonicalHEPDataW3T43RunnerPerBinNonCollapseReceipt ="
    start = agda_text.index(marker)
    end_marker = "\ncanonicalHEPDataW3T43RunnerPerBinWitnessPullNonZero"
    end = agda_text.index(end_marker, start)
    return agda_text[start:end]


def _agda_field(body: str, field_name: str) -> str:
    pattern = rf"(?:\{{|;)\s*{re.escape(field_name)}\s*=\s*\n\s*([^\n]+)"
    match = re.search(pattern, body)
    if not match:
        raise ValueError(f"missing Agda field {field_name}")
    return match.group(1).strip()


def _agda_float(body: str, field_name: str) -> float:
    return float(_agda_field(body, field_name))


def _agda_string(body: str, field_name: str) -> str:
    raw = _agda_field(body, field_name)
    _require(
        raw.startswith('"') and raw.endswith('"'),
        f"Agda field {field_name} is not a string literal: {raw}",
    )
    return raw[1:-1]


def validate_w3_noncollapse_receipt(
    comparison_path: Path = DEFAULT_COMPARISON_PATH,
    agda_path: Path = DEFAULT_AGDA_PATH,
    provider_checksums_path: Path = DEFAULT_PROVIDER_CHECKSUMS_PATH,
    expected_comparison_sha256: str = EXPECTED_COMPARISON_SHA256,
) -> dict[str, Any]:
    comparison_sha = sha256_file(comparison_path)
    _require(
        comparison_sha == expected_comparison_sha256,
        "comparison artifact checksum mismatch: "
        f"expected {expected_comparison_sha256}, got {comparison_sha}",
    )

    payload = _load_json(comparison_path)
    comparison = payload["comparison"]
    noncollapse = payload["nonCollapseWitness"]
    witness = noncollapse["witness"]
    per_bin = payload["perBin"]
    promotion = payload["promotionBoundary"]

    _require(comparison["status"] == "candidate-pass-no-authority-token", "bad status")
    _require(comparison["candidateOnly"] is True, "comparison must stay candidate-only")
    _require_close(float(comparison["chi2PerDof"]), 2.1565191176275618, "chi2PerDof")
    _require(len(per_bin) == 18, "perBin must contain exactly 18 rows")

    max_pull_row = max(per_bin, key=lambda row: abs(float(row["pull"])))
    _require(max_pull_row["binIndex"] == EXPECTED_WITNESS["binIndex"], "wrong witness bin")
    for field, expected in EXPECTED_WITNESS.items():
        _require_close(float(witness[field]), float(expected), f"witness.{field}")
        row_field = "covarianceSigma" if field == "covarianceSigma" else field
        _require_close(float(max_pull_row[row_field]), float(expected), f"perBin.{field}")

    _require(noncollapse["status"] == "runner-per-bin-candidate-witness", "bad witness status")
    _require(noncollapse["witnessPullNonZero"] is True, "witness pull must be non-zero")
    _require(noncollapse["witnessPredDataDistinct"] is True, "prediction/data must differ")
    _require(
        noncollapse["providerGradePayloadPresent"] is False,
        "provider-grade non-collapse must remain absent locally",
    )
    _require(
        noncollapse["externalNonCollapseWitnessReceiptConstructed"] is False,
        "external non-collapse receipt must not be constructed locally",
    )
    _require(
        promotion["w3AcceptedEvidenceAuthorityTokenConstructed"] is False,
        "W3AcceptedEvidenceAuthorityToken must not be constructed locally",
    )
    _require(
        promotion["w3AcceptedAuthorityExternalReceiptConstructed"] is False,
        "W3 accepted external authority receipt must not be constructed locally",
    )

    residual = float(witness["prediction"]) - float(witness["data"])
    _require_close(residual, float(witness["residual"]), "computed residual")
    _require_close(
        residual / float(witness["covarianceSigma"]),
        float(witness["pull"]),
        "computed pull",
    )

    agda_body = _canonical_runner_record_body(agda_path.read_text(encoding="utf-8"))
    _require(
        _agda_field(agda_body, "status") == "perBinRunnerWitnessExtracted",
        "Agda runner status is not extracted",
    )
    _require(_agda_field(agda_body, "witnessPullNonZero") == "true", "Agda pull flag")
    _require(
        _agda_field(agda_body, "witnessPredDataDistinct") == "true",
        "Agda pred/data flag",
    )
    _require(
        _agda_field(agda_body, "authorityTokenConstructedHere") == "false",
        "Agda authority token field must remain false",
    )
    _require(
        _agda_field(agda_body, "acceptedAuthorityExternalReceiptConstructedHere")
        == "false",
        "Agda accepted external authority receipt field must remain false",
    )
    _require_close(_agda_float(agda_body, "nBins"), 18.0, "Agda nBins")
    _require_close(
        _agda_float(agda_body, "witnessBinIndex"),
        float(EXPECTED_WITNESS["binIndex"]),
        "Agda witnessBinIndex",
    )
    _require_close(
        _agda_float(agda_body, "witnessPhiStar"),
        float(EXPECTED_WITNESS["phiStar"]),
        "Agda witnessPhiStar",
    )
    _require_close(
        _agda_float(agda_body, "witnessPhiStarLow"),
        float(EXPECTED_WITNESS["phiStarLow"]),
        "Agda witnessPhiStarLow",
    )
    _require_close(
        _agda_float(agda_body, "witnessPhiStarHigh"),
        float(EXPECTED_WITNESS["phiStarHigh"]),
        "Agda witnessPhiStarHigh",
    )
    _require_close(
        _agda_float(agda_body, "witnessPrediction"),
        float(EXPECTED_WITNESS["prediction"]),
        "Agda witnessPrediction",
    )
    _require_close(
        _agda_float(agda_body, "witnessData"),
        float(EXPECTED_WITNESS["data"]),
        "Agda witnessData",
    )
    _require_close(
        _agda_float(agda_body, "witnessUncertainty"),
        float(EXPECTED_WITNESS["covarianceSigma"]),
        "Agda witnessUncertainty",
    )
    _require_close(
        _agda_float(agda_body, "witnessPull"),
        float(EXPECTED_WITNESS["pull"]),
        "Agda witnessPull",
    )
    _require_close(
        _agda_float(agda_body, "comparisonChi2PerDof"),
        2.1565191176,
        "Agda comparisonChi2PerDof",
    )
    _require(
        _agda_string(agda_body, "priorArtifactSha256")
        == payload["sourceProjection"]["sha256"],
        "Agda priorArtifactSha256 must bind source projection checksum",
    )

    checksums = _read_checksum_manifest(provider_checksums_path)
    t43_relpath = "logs/research/provider_inputs/hepdata_ins2079374/t43_canonical.json"
    t44_relpath = "logs/research/provider_inputs/hepdata_ins2079374/t44_canonical.json"
    _require(checksums[t43_relpath] == EXPECTED_T43_CANONICAL_SHA256, "t43 checksum entry")
    _require(checksums[t44_relpath] == EXPECTED_T44_CANONICAL_SHA256, "t44 checksum entry")
    _require(sha256_file(ROOT / t43_relpath) == EXPECTED_T43_CANONICAL_SHA256, "t43 sha")
    _require(sha256_file(ROOT / t44_relpath) == EXPECTED_T44_CANONICAL_SHA256, "t44 sha")

    return {
        "status": "ok",
        "comparison_sha256": comparison_sha,
        "witness_bin": witness["binIndex"],
        "witness_pull": witness["pull"],
        "provider_grade_payload_present": noncollapse["providerGradePayloadPresent"],
        "authority_token_constructed": promotion[
            "w3AcceptedEvidenceAuthorityTokenConstructed"
        ],
    }


def main() -> int:
    parser = argparse.ArgumentParser(
        description="Fail-closed W3 t43 non-collapse runner receipt checker."
    )
    parser.add_argument("--comparison", type=Path, default=DEFAULT_COMPARISON_PATH)
    parser.add_argument("--agda", type=Path, default=DEFAULT_AGDA_PATH)
    parser.add_argument(
        "--provider-checksums", type=Path, default=DEFAULT_PROVIDER_CHECKSUMS_PATH
    )
    args = parser.parse_args()

    result = validate_w3_noncollapse_receipt(
        comparison_path=args.comparison,
        agda_path=args.agda,
        provider_checksums_path=args.provider_checksums,
    )
    print(json.dumps(result, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
