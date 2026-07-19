from __future__ import annotations

from pathlib import Path
import sys

import numpy as np

SCRIPTS = Path(__file__).resolve().parents[1]
if str(SCRIPTS) not in sys.path:
    sys.path.insert(0, str(SCRIPTS))

from ns_compact_gamma_multitriad_evolved_audit import (  # noqa: E402
    angular_packet_metrics,
    audit_family,
    disjoint_orientations,
    multitriad_diffuse_hat,
)


def test_disjoint_orientations_have_projectively_disjoint_support() -> None:
    orientations = disjoint_orientations(4, 1)
    assert len(orientations) == 4
    supports: list[set[tuple[int, int, int]]] = []
    base_modes = (
        np.asarray((3, 0, 1), dtype=int),
        np.asarray((0, 3, 1), dtype=int),
        np.asarray((3, 3, 2), dtype=int),
    )
    for matrix in orientations:
        support: set[tuple[int, int, int]] = set()
        for base in base_modes:
            mode = tuple(int(value) for value in matrix @ base)
            first = next(value for value in mode if value != 0)
            support.add(mode if first > 0 else tuple(-value for value in mode))
        supports.append(support)
    for left_index, left in enumerate(supports):
        for right in supports[left_index + 1 :]:
            assert not left.intersection(right)


def test_multitriad_packet_is_real_divergence_free_and_angularly_nontrivial() -> None:
    raw, metadata = multitriad_diffuse_hat(
        24,
        2,
        triad_count=4,
        input_amplitude=0.1,
        target_ratio=2.5,
        satellite_fraction=0.55,
        phase_spread=0.25,
        seed=3,
    )
    field = np.fft.ifftn(raw, axes=(0, 1, 2))
    metrics = angular_packet_metrics(raw, 2)
    assert metadata["triad_count"] == 4
    assert float(np.max(np.abs(field.imag))) < 1.0e-12
    assert metrics["active_projective_mode_count"] >= 4
    assert metrics["angular_participation_dimension"] > 1.1
    assert metrics["relative_divergence_residual"] < 1.0e-10


def test_small_evolved_audit_is_complete_and_nonpromoting() -> None:
    result = audit_family(
        search_cutoff=24,
        verify_cutoffs=(24,),
        target_shells=(2,),
        nu=0.01,
        input_amplitude=0.1,
        triad_counts=(2,),
        phase_spreads=(0.0,),
        target_ratios=(2.5,),
        satellite_fraction=0.5,
        seeds=(0,),
        gamma_threshold=0.5,
        minimum_angular_participation=1.05,
        verify_count=1,
        end_parabolic_time=0.0002,
        output_count=2,
        cfl=0.2,
    )
    assert result["configuration_count"] == 1
    assert result["search_row_count"] == 1
    assert result["selected_configuration_count"] in (0, 1)
    assert result["authority"]["finite_galerkin_multitriad_audit"] is True
    assert result["authority"]["cutoff_shell_uniform_authority"] is False
    assert result["authority"]["theorem_authority"] is False
    assert result["authority"]["clay_authority"] is False
    assert result["authority"]["promoted"] is False
