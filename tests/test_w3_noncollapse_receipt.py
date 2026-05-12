from __future__ import annotations

import json
from pathlib import Path
import sys

import pytest

ROOT = Path(__file__).resolve().parents[1]
if str(ROOT) not in sys.path:
    sys.path.insert(0, str(ROOT))

from scripts.check_w3_noncollapse_receipt import (  # type: ignore[import-not-found]
    DEFAULT_COMPARISON_PATH,
    sha256_file,
    validate_w3_noncollapse_receipt,
)


def test_w3_noncollapse_runner_receipt_matches_json_and_agda() -> None:
    result = validate_w3_noncollapse_receipt()

    assert result["status"] == "ok"
    assert result["witness_bin"] == 12
    assert result["provider_grade_payload_present"] is False
    assert result["authority_token_constructed"] is False


def test_w3_noncollapse_checker_rejects_local_provider_grade_claim(
    tmp_path: Path,
) -> None:
    payload = json.loads(DEFAULT_COMPARISON_PATH.read_text(encoding="utf-8"))
    payload["nonCollapseWitness"]["providerGradePayloadPresent"] = True
    mutated = tmp_path / "mutated.json"
    mutated.write_text(json.dumps(payload, sort_keys=True), encoding="utf-8")

    with pytest.raises(ValueError, match="provider-grade non-collapse"):
        validate_w3_noncollapse_receipt(
            comparison_path=mutated,
            expected_comparison_sha256=sha256_file(mutated),
        )
