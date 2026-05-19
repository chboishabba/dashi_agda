from __future__ import annotations

from dataclasses import dataclass

from prototype_schema import NumericObservables


@dataclass
class ExplanationScore:
    residual_ratio: float
    mdl_penalty: float
    confidence_penalty: float
    explanation_cost: float
    interpretation: str


def confidence_penalty(confidence: str) -> float:
    penalties = {
        "surrogate-aligned": 0.0,
        "surrogate-uncertain": 0.25,
        "surrogate-mismatch": 0.75,
    }
    return penalties.get(confidence, 0.5)


def score_explanation(
    observables: NumericObservables,
    *,
    residual: float,
    confidence: str,
    mdl_weight: float = 0.2,
    defect_floor: float = 1.0e-9,
) -> ExplanationScore:
    scale = max(observables.promoted_d0, defect_floor)
    residual_ratio = abs(residual) / scale
    mdl_pen = mdl_weight * max(observables.mdl_level, 0.0)
    conf_pen = confidence_penalty(confidence)
    explanation_cost = residual_ratio + mdl_pen + conf_pen

    if explanation_cost < 0.35:
        interpretation = "strong-internal-explanation"
    elif explanation_cost < 1.0:
        interpretation = "mixed-internal-explanation"
    else:
        interpretation = "weak-internal-explanation"

    return ExplanationScore(
        residual_ratio=residual_ratio,
        mdl_penalty=mdl_pen,
        confidence_penalty=conf_pen,
        explanation_cost=explanation_cost,
        interpretation=interpretation,
    )
