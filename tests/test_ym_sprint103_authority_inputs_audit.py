from __future__ import annotations

import json
import re
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "ym_sprint103_authority_inputs_audit.py"
AGDA = REPO_ROOT / "DASHI" / "Physics" / "Closure" / "YMSprint103AuthorityInputs.agda"
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint103_authority_inputs"
    / "ym_sprint103_authority_inputs_summary.json"
)

EXPECTED_INPUTS = {
    "BalabanCMP98LocalOscillationBound",
    "BalabanCMP98AveragingKernelIsProbability",
    "BalabanCMP116PolymerMassBound",
}


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint103_inhabits_authority_inputs_one_to_three_only() -> None:
    summary = run_script()
    names = {item["lemma"] for item in summary["authority_inputs"]}

    assert summary["implemented_authority_input_count"] == 3
    assert names == EXPECTED_INPUTS
    assert summary["implemented_only_inputs_1_to_3"] is True
    assert all(item["authority_input_inhabited"] is True for item in summary["authority_inputs"])
    assert all(item["source_present"] is True for item in summary["authority_inputs"])
    assert all(item["proof_argument_present"] is True for item in summary["authority_inputs"])


def test_sprint103_keeps_later_obligations_and_clay_fail_closed() -> None:
    summary = run_script()

    assert summary["empty_data_types_introduced"] is False
    assert summary["downstream_sprint102_obligations_still_open"] is True
    assert summary["clay_yang_mills_promoted"] is False
    assert (
        summary["route_decision"]
        == "SPRINT103_INHABITS_AUTHORITY_INPUTS_1_2_3_ONLY_NO_PROMOTION"
    )


def test_sprint103_agda_has_inhabited_records_and_no_empty_data_types() -> None:
    source = AGDA.read_text()

    for name in EXPECTED_INPUTS:
        assert f"record {name} : Set where" in source
        assert f"canonical{name} :" in source

    assert source.count("proofArgument :") == 3
    assert source.count("source :") == 3
    assert "clayYangMillsPromoted = false" in source
    assert not re.search(r"^data\s+\S+.*where\s*$", source, flags=re.MULTILINE)
