#!/usr/bin/env python3
"""Run the off-packet Schur audit with deterministic far-low-shell probes.

The base audit evaluates path and Navier-Stokes RHS tangents.  Those tangents
were effectively supported inside |j-K| <= 1 on the declared family, so the
explicit tail term was not exercised.  This driver adds a reality-closed,
divergence-free tangent on shell K-2 for every sampled state.  The state is
unchanged; only the differential direction is expanded.
"""
from __future__ import annotations

import hashlib
import math
from typing import Any

import numpy as np

import ns_compact_gamma_offpacket_schur_audit as audit
from ns_compact_gamma_common_u_net_audit import nearest_center
from ns_compact_gamma_differential_modulus_audit import (
    dangerous_rows,
    path_state_tangent,
)
from ns_compact_gamma_pathwise_retention_audit import state_at_time
from ns_compact_gamma_potential_audit import _state_geometry
from ns_galerkin_coherence_core import leray_project_hat


_original_response_rows = audit.response_rows
_original_audit_family = audit.audit_family


def deterministic_seed(*parts: object) -> int:
    raw = "|".join(str(part) for part in parts).encode("utf-8")
    return int.from_bytes(hashlib.sha256(raw).digest()[:8], "big", signed=False)


def far_low_shell_probe(
    geometry: dict[str, Any], *, target_shell: int, seed: int
) -> tuple[np.ndarray, dict[str, float | int]]:
    """Construct a normalized real, divergence-free probe on shell K-2."""
    probe_shell = target_shell - 2
    if probe_shell < 0:
        raise ValueError("far-low probe requires target shell at least two")
    n = int(geometry["cutoff"])
    rng = np.random.default_rng(seed)
    physical = rng.standard_normal((n, n, n, 3))
    raw = np.fft.fftn(physical, axes=(0, 1, 2))
    indices = audit.shell_index(np.sqrt(geometry["norm_sq"]))
    mask = geometry["dealias"] & (indices == probe_shell)
    probe = leray_project_hat(
        raw * mask[..., None], geometry["wave"], geometry["norm_sq"]
    )
    coefficient = probe / float(n ** 3)
    modal = np.sum(np.abs(coefficient) ** 2, axis=-1)
    xk_square = float(np.sum(
        modal * (
            1.0
            + float(2 ** (-2 * target_shell)) * geometry["norm_sq"]
        )
    ))
    if xk_square <= 1.0e-30:
        raise ValueError("far-low probe shell is empty")
    probe /= math.sqrt(xk_square)
    divergence = float(np.max(np.abs(np.einsum(
        "...i,...i->...", geometry["wave"], probe
    ))))
    reality = float(np.max(np.abs(
        np.fft.ifftn(probe, axes=(0, 1, 2)).imag
    )))
    return probe, {
        "probe_shell": probe_shell,
        "shell_offset": -2,
        "mode_count": int(np.count_nonzero(mask)),
        "pre_normalization_XK_norm": math.sqrt(xk_square),
        "divergence_residual": divergence,
        "reality_residual": reality,
    }


def response_rows_with_far_probe(
    profiles: list[dict[str, Any]],
    centers: list[dict[str, Any]],
    trajectories: dict[str, list[dict[str, Any]]],
    *,
    nu: float,
    target_energy: float,
    path_parameters: tuple[float, ...],
    times_per_profile: int,
    tangent_kinds: tuple[str, ...],
) -> list[dict[str, Any]]:
    requested_far = "far-low" in tangent_kinds
    base_kinds = tuple(kind for kind in tangent_kinds if kind != "far-low")
    unknown = set(tangent_kinds) - {"path", "rhs", "far-low"}
    if unknown:
        raise ValueError(f"unsupported tangent kinds: {sorted(unknown)}")
    rows = _original_response_rows(
        profiles,
        centers,
        trajectories,
        nu=nu,
        target_energy=target_energy,
        path_parameters=path_parameters,
        times_per_profile=times_per_profile,
        tangent_kinds=base_kinds,
    ) if base_kinds else []
    if not requested_far:
        return rows

    for profile in profiles:
        center, _distance = nearest_center(profile, centers)
        shell = int(profile["target_shell"])
        for trajectory_row in dangerous_rows(profile, times_per_profile):
            tau = float(trajectory_row["parabolic_time"])
            member_raw = state_at_time(trajectories[profile["profile_id"]], tau)
            center_raw = state_at_time(trajectories[center["profile_id"]], tau)
            for parameter in path_parameters:
                state, _path_tangent, normalization_residual = path_state_tangent(
                    center_raw,
                    member_raw,
                    parameter,
                    nu=nu,
                    shell=shell,
                    target_energy=target_energy,
                )
                geometry = _state_geometry(state, nu, shell)
                probe, metadata = far_low_shell_probe(
                    geometry,
                    target_shell=shell,
                    seed=deterministic_seed(
                        profile["profile_id"], tau, parameter, "far-low"
                    ),
                )
                rows.append({
                    "profile_id": profile["profile_id"],
                    "center_profile_id": center["profile_id"],
                    "cutoff": int(profile["cutoff"]),
                    "target_shell": shell,
                    "parabolic_time": tau,
                    "path_parameter": float(parameter),
                    "tangent_kind": "far-low",
                    "normalization_residual": normalization_residual,
                    "probe_metadata": metadata,
                    "response": audit.off_response(
                        state, probe, nu=nu, shell=shell
                    ),
                })
    return rows


def audit_family_with_tail_candidate(**kwargs: Any) -> dict[str, Any]:
    result = _original_audit_family(**kwargs)
    minimum_radius = min(int(value) for value in kwargs["tail_radii"])
    explicit = [
        candidate for candidate in result["candidates"]
        if int(candidate["tail_radius"]) == minimum_radius
        and bool(candidate["full_chain_survives"])
    ]
    explicit.sort(key=lambda candidate: (
        float(candidate["holdout_evaluation"]["maximum_tail_quotient"]),
        float(candidate["matched_evaluation"]["maximum_tail_quotient"]),
        float(candidate["fitted_near_schur_constant"]),
        float(candidate["shell_exponent"]),
        float(candidate["angular_eta"]),
    ))
    result["explicit_tail_candidate"] = explicit[0] if explicit else None
    result["far_low_probe_authority"] = {
        "deterministic_reality_closed_probe": True,
        "probe_shell_offset": -2,
        "tail_exercised_for_minimum_radius": bool(explicit),
        "all_tangent_directions_controlled": False,
        "promoted": False,
    }
    return result


def install_driver() -> None:
    audit.response_rows = response_rows_with_far_probe
    audit.audit_family = audit_family_with_tail_candidate


def main() -> None:
    install_driver()
    audit.main()


if __name__ == "__main__":
    main()
