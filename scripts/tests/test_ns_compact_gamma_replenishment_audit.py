from __future__ import annotations

from pathlib import Path
import math
import sys

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_compact_gamma_adversarial_sweep import phased_triad_hat  # noqa: E402
from ns_compact_gamma_potential_audit import compact_gamma_snapshot  # noqa: E402
from ns_compact_gamma_replenishment_audit import (  # noqa: E402
    audit_family,
    mechanism_accounting,
)


def test_mechanism_accounting_recovers_signed_derivative() -> None:
    raw = phased_triad_hat(16, 0.1, 1.0, 0.25, -0.5 * math.pi)
    snapshot = compact_gamma_snapshot(raw, 0.01, 2)
    result = mechanism_accounting(snapshot)
    assert result["mechanism_balance_residual"] < 1.0e-12
    assert result["escape_supply"] > result["replenishment"]
    assert 0.0 <= result["replenishment_over_escape"] < 1.0
    assert result["strict_absorption_margin"] > 0.0


def test_small_family_produces_nonpromoting_absorption_receipt() -> None:
    result = audit_family(
        search_cutoff=16,
        verify_cutoffs=(16,),
        nu=0.01,
        shell=2,
        input_amplitude=0.1,
        input_ratios=(1.0,),
        target_amplitudes=(0.25,),
        phase_count=4,
        gamma_threshold=0.5,
        verify_count=1,
    )
    assert result["search_row_count"] == 4
    assert result["dangerous_row_count"] >= 1
    assert result["sampled_theta_envelope"] is not None
    assert result["maximum_mechanism_balance_residual"] < 1.0e-10
    assert result["authority"]["theorem_authority"] is False
    assert result["authority"]["promoted"] is False
