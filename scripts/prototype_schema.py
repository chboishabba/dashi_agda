from __future__ import annotations

import math
from dataclasses import dataclass
from typing import Any


@dataclass
class DashiStateSchema:
    trace_id: str
    delta: list[float]
    coarse_head: list[float]
    mdl_level: float
    photon_energy: float


@dataclass
class NumericObservables:
    trace_id: str
    delta_defect: float
    promoted_d0: float
    g_star: float
    q_s: float
    photon_energy: float
    mdl_level: float


@dataclass
class MeasurementSurface:
    trace_id: str
    x: list[float]
    y: list[float]
    cov: list[list[float]]


def coerce_float_list(value: Any, name: str) -> list[float]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a list")
    return [float(item) for item in value]


def coerce_float_matrix(value: Any, name: str) -> list[list[float]]:
    if not isinstance(value, list):
        raise ValueError(f"{name} must be a matrix encoded as a list of rows")

    matrix: list[list[float]] = []
    for index, row in enumerate(value):
        if not isinstance(row, list):
            raise ValueError(f"{name}[{index}] must be a list")
        matrix.append([float(item) for item in row])
    return matrix


def load_state_schema(state: dict[str, Any]) -> DashiStateSchema:
    return DashiStateSchema(
        trace_id=str(state.get("trace_id", "anonymous-trace")),
        delta=coerce_float_list(state.get("delta", []), "delta"),
        coarse_head=coerce_float_list(state.get("coarse_head", []), "coarse_head"),
        mdl_level=float(state.get("mdl_level", 0.0)),
        photon_energy=float(state.get("photon_energy", state.get("omega_photon", 1.0))),
    )


def load_measurement_surface(
    measurement: dict[str, Any],
    *,
    trace_id: str = "anonymous-measurement",
) -> MeasurementSurface:
    if str(measurement.get("status", "missing")) != "ok":
        raise ValueError("measurement payload must have status='ok'")

    field_status = measurement.get("field_status", {})
    if not isinstance(field_status, dict):
        raise ValueError("measurement.field_status must be a mapping")

    required_fields = ("x", "y", "cov")
    missing = [
        field
        for field in required_fields
        if str(field_status.get(field, "missing")) != "ok"
    ]
    if missing:
        raise ValueError(
            "measurement payload is missing required fields: "
            + ", ".join(sorted(missing))
        )

    x = coerce_float_list(measurement.get("x", []), "measurement.x")
    y = coerce_float_list(measurement.get("y", []), "measurement.y")
    cov = coerce_float_matrix(measurement.get("cov", []), "measurement.cov")

    if len(x) != len(y):
        raise ValueError("measurement.x and measurement.y must have the same length")
    if len(cov) != len(x):
        raise ValueError("measurement.cov row count must match measurement.x length")
    for index, row in enumerate(cov):
        if len(row) != len(x):
            raise ValueError(
                f"measurement.cov row {index} must have length {len(x)}"
            )

    return MeasurementSurface(
        trace_id=trace_id,
        x=x,
        y=y,
        cov=cov,
    )


def vector_norm(values: list[float]) -> float:
    return math.sqrt(sum(component * component for component in values))


def extract_numeric_observables(
    schema: DashiStateSchema,
    *,
    mdl_lambda: float,
    alpha_qs: float,
) -> NumericObservables:
    delta_defect = vector_norm(schema.delta)
    tau = float(schema.delta[0]) if schema.delta else 0.0
    aligned_spatial = sum(abs(component) for component in schema.coarse_head)

    promoted_d0 = abs(tau) + 0.5 * aligned_spatial
    g_star = promoted_d0 / (1.0 + mdl_lambda * max(schema.mdl_level, 0.0))
    q_s = max(g_star, 0.0) ** alpha_qs

    return NumericObservables(
        trace_id=schema.trace_id,
        delta_defect=delta_defect,
        promoted_d0=promoted_d0,
        g_star=g_star,
        q_s=q_s,
        photon_energy=schema.photon_energy,
        mdl_level=schema.mdl_level,
    )
