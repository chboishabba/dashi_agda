from __future__ import annotations

import math
from dataclasses import dataclass

from prototype_schema import NumericObservables


@dataclass
class GBWParameters:
    lambda_gbw: float
    x0: float
    sigma0: float
    thickness: float
    normalization_d0: float
    sqrt_s: float
    defect_floor: float


@dataclass
class GBWResponse:
    x_ref: float
    q_s_sq: float
    dipole_size: float
    sigma_dipole: float
    predicted_yield: float
    residual: float
    confidence: str


def gbw_response(obs: NumericObservables, params: GBWParameters) -> GBWResponse:
    x_ref = obs.photon_energy / max(params.sqrt_s, params.defect_floor)
    x_ref = max(x_ref, params.defect_floor)

    q_s_sq = ((x_ref / params.x0) ** (-params.lambda_gbw)) * params.thickness * max(obs.q_s, params.defect_floor)
    dipole_size = 1.0 / math.sqrt(max(obs.delta_defect, params.defect_floor))
    sigma_dipole = params.sigma0 * (1.0 - math.exp(-(dipole_size * dipole_size * q_s_sq) / 4.0))

    predicted_yield = params.normalization_d0 * (
        1.0 - math.exp(-max(obs.promoted_d0, 0.0) / max(sigma_dipole, params.defect_floor))
    )
    residual = obs.promoted_d0 - predicted_yield

    residual_scale = max(obs.promoted_d0, params.defect_floor)
    if abs(residual) < 0.1 * residual_scale:
        confidence = "surrogate-aligned"
    elif abs(residual) < 0.5 * residual_scale:
        confidence = "surrogate-uncertain"
    else:
        confidence = "surrogate-mismatch"

    return GBWResponse(
        x_ref=x_ref,
        q_s_sq=q_s_sq,
        dipole_size=dipole_size,
        sigma_dipole=sigma_dipole,
        predicted_yield=predicted_yield,
        residual=residual,
        confidence=confidence,
    )
