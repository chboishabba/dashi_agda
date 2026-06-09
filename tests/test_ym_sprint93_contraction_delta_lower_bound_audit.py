from __future__ import annotations

import json
import math
import subprocess
from pathlib import Path


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = (
    REPO_ROOT
    / "scripts"
    / "ym_sprint93_contraction_delta_lower_bound_audit.py"
)
SUMMARY = (
    REPO_ROOT
    / "outputs"
    / "ym_sprint93_contraction_delta_lower_bound"
    / "ym_sprint93_contraction_delta_lower_bound_summary.json"
)


def run_script() -> dict:
    subprocess.run(["python", str(SCRIPT)], cwd=REPO_ROOT, check=True)
    return json.loads(SUMMARY.read_text())


def test_sprint93_closes_scoped_balaban_inputs_and_lower_bound() -> None:
    summary = run_script()

    assert summary["balaban_cmp98_kernel_probability_scoped_authority_accepted"] is True
    assert summary["balaban_cmp116_polymer_mass_bound_scoped_authority_accepted"] is True
    assert summary["contraction_delta_lower_bound_closed_in_repo"] is True
    assert summary["old_contraction_delta_a_independent_framing_retired"] is True


def test_sprint93_delta_min_is_positive_and_matches_formula() -> None:
    summary = run_script()

    assert summary["delta_min_formula"] == "1 - exp(-4)"
    assert math.isclose(summary["delta_min_numeric"], 1.0 - math.exp(-4))
    assert summary["delta_min_numeric"] > 0.98
    assert summary["c_local_limit_as_a_to_zero"] == 0.0


def test_sprint93_remaining_open_lemmas_are_fail_closed() -> None:
    summary = run_script()

    assert summary["remaining_open_lemmas"] == [
        "UniformBoundForAllA",
        "WC3UniformInA",
        "UniformConnectedSchwingerDecay",
        "ContinuumLimitMassGap",
        "Nontrivial4DSU3YangMillsMeasure",
        "ClayStatementBoundaryDischarged",
        "ExternalAcceptanceToken",
    ]
    assert summary["uniform_bound_for_all_a_derived_in_repo"] is False
    assert summary["wc3_uniform_in_a_derived_in_repo"] is False
    assert summary["uniform_connected_schwinger_decay_derived_in_repo"] is False
    assert summary["continuum_limit_mass_gap_derived_in_repo"] is False
    assert summary["clay_yang_mills_promoted"] is False
