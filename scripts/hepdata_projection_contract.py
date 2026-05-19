#!/usr/bin/env python3
from __future__ import annotations

from dataclasses import dataclass, field
from typing import Literal

try:
    from prototype_schema import MeasurementSurface  # type: ignore[import-not-found]
except ModuleNotFoundError:
    from scripts.prototype_schema import MeasurementSurface

ProjectionStatus = Literal["ok", "degraded", "rejected"]
TransformKind = Literal["raw", "gradient", "whitened", "other-declared"]


@dataclass(frozen=True)
class TransformSpec:
    name: TransformKind
    preconditions: list[str]
    meaning: str
    preserves_metric_geometry: bool
    requires_regularization: bool
    comparable_group: str
    downstream_use: str


TRANSFORM_VOCAB: dict[TransformKind, TransformSpec] = {
    "raw": TransformSpec(
        name="raw",
        preconditions=[
            "valid x/y/cov measurement surface",
            "metric_ready=true",
        ],
        meaning="Use observed y as the candidate signal without reparameterizing the carrier.",
        preserves_metric_geometry=True,
        requires_regularization=False,
        comparable_group="native",
        downstream_use="Exploratory only unless explicitly promoted by a later lane.",
    ),
    "gradient": TransformSpec(
        name="gradient",
        preconditions=[
            "ordered x coordinates",
            "finite x spacing",
            "valid covariance metric",
            "declared derivative rule",
        ],
        meaning="Use local variation of y over x as the candidate signal.",
        preserves_metric_geometry=False,
        requires_regularization=False,
        comparable_group="derived",
        downstream_use="Only with an explicit derivative/covariance propagation law.",
    ),
    "whitened": TransformSpec(
        name="whitened",
        preconditions=[
            "full-rank covariance or declared regularization",
            "explicit whitening operator recorded in diagnostics",
        ],
        meaning="Transform the candidate signal into covariance-normalized coordinates.",
        preserves_metric_geometry=False,
        requires_regularization=True,
        comparable_group="normalized",
        downstream_use="Comparison only within the declared whitened frame.",
    ),
    "other-declared": TransformSpec(
        name="other-declared",
        preconditions=[
            "explicit transform name and semantics",
            "declared metric propagation law",
        ],
        meaning="Use a lane-specific transform that has been explicitly named and documented.",
        preserves_metric_geometry=False,
        requires_regularization=False,
        comparable_group="declared-other",
        downstream_use="None by default until the lane declares downstream permissions.",
    ),
}


@dataclass
class DeltaStateContract:
    """
    Contract-only carrier for a future MeasurementSurface -> DeltaState
    interpretation.

    This is intentionally not a theorem object and not an implementation.
    It exists only to pin the minimum fields and failure surfaces that any
    future projection must make explicit.
    """

    trace_id: str
    delta: list[float]
    metric: list[list[float]]
    local_energy: list[float]
    total_energy: float
    confidence: list[float]


@dataclass
class ProjectionDiagnostics:
    condition_number: float | None = None
    covariance_rank: int | None = None
    transform_name: TransformKind = "other-declared"
    transform_preconditions: list[str] = field(default_factory=list)
    transform_preserves_metric_geometry: bool | None = None
    transform_requires_regularization: bool | None = None
    transform_downstream_use: str = "undeclared"
    delta_definition: str = "undeclared"
    notes: list[str] = field(default_factory=list)


@dataclass
class ProjectionResultContract:
    status: ProjectionStatus
    diagnostics: ProjectionDiagnostics
    delta_state: DeltaStateContract | None = None
    rejection_reason: str | None = None
    claim_boundary: str = (
        "Contract only. No projection implementation, no theorem promotion, "
        "no implicit covariance drop, and no silent Δ interpretation."
    )


def projection_contract_summary() -> dict[str, object]:
    return {
        "input": "MeasurementSurface",
        "output": "ProjectionResultContract",
        "declared_transform_vocabulary": {
            name: {
                "preconditions": spec.preconditions,
                "meaning": spec.meaning,
                "preserves_metric_geometry": spec.preserves_metric_geometry,
                "requires_regularization": spec.requires_regularization,
                "comparable_group": spec.comparable_group,
                "downstream_use": spec.downstream_use,
            }
            for name, spec in TRANSFORM_VOCAB.items()
        },
        "admissibility_conditions": [
            "measurement surface is shape-valid",
            "covariance law is declared",
            "delta definition is declared",
            "declared transform vocabulary governs the selected transform",
        ],
        "hard_failures": [
            "missing covariance metric",
            "undeclared transform",
            "silent whitening",
            "silent covariance drop",
            "undeclared delta/coarse_head semantics",
        ],
        "claim_boundary": (
            "This module is a contract stub only. Future projection code must "
            "satisfy the contract explicitly."
        ),
    }


def assert_projection_preconditions(surface: MeasurementSurface) -> None:
    """
    Minimal precondition hook for future projection lanes.

    It is intentionally conservative and does not attempt any projection.
    """

    point_count = len(surface.x)
    if point_count != len(surface.y):
        raise ValueError("measurement surface must have aligned x/y dimensions")
    if point_count != len(surface.cov):
        raise ValueError("measurement surface covariance row count mismatch")
    for index, row in enumerate(surface.cov):
        if len(row) != point_count:
            raise ValueError(
                f"measurement surface covariance row {index} length mismatch"
            )
