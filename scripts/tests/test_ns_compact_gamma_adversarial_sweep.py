from __future__ import annotations

from pathlib import Path
import math
import sys

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_compact_gamma_adversarial_sweep import (  # noqa: E402
    phased_triad_hat,
    sweep,
)
from ns_compact_gamma_potential_audit import compact_gamma_snapshot  # noqa: E402


def test_original_phase_recovers_positive_transfer_lane() -> None:
    raw = phased_triad_hat(16, 0.1, 1.0, 0.25, -0.5 * math.pi)
    result = compact_gamma_snapshot(raw, 0.01, 2)
    assert result["gamma"] > 0.5
    assert result["positive_part_branch"] == "strict_positive_transfer"


def test_reality_closed_phased_triad() -> None:
    raw = phased_triad_hat(16, 0.1, 0.5, 0.2, 0.3)
    field = np.fft.ifftn(raw, axes=(0, 1, 2))
    assert float(np.max(np.abs(field.imag))) < 1.0e-12


def test_small_adversarial_sweep_is_complete_and_non_promoting() -> None:
    result = sweep(
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
    assert result["matched_adverse_candidates"]
    assert result["authority"]["universal_pointwise_implication_proved"] is False
    assert result["authority"]["promoted"] is False
