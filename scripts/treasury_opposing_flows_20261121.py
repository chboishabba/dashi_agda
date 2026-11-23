"""Synthetic opposing-channel Treasury yield stress reference.

All inputs are pressure contributions on a *declared common basis*, not
measured bp, dollar flows, elasticities, probabilities or trading signals.
Reuses the public Agda structural cut; real inference requires matched data.
"""
from __future__ import annotations
from dataclasses import dataclass
from enum import Enum
from math import isfinite


class YieldSign(str, Enum):
    DOWN = "down"
    FLAT = "flat"
    UP = "up"


@dataclass(frozen=True)
class OpposingFlows:
    haven_buying: float
    easing_expectation: float
    japan_repatriation: float
    treasury_forced_sales: float
    supply_term_premium: float
    common_basis_receipt: bool = False

    def __post_init__(self) -> None:
        contributions = (self.haven_buying, self.easing_expectation,
                         self.japan_repatriation, self.treasury_forced_sales,
                         self.supply_term_premium)
        if any(not isfinite(v) or v < 0 for v in contributions):
            raise ValueError("pressure contributions must be finite and nonnegative")

    @property
    def downward(self) -> float:
        return self.haven_buying + self.easing_expectation

    @property
    def upward(self) -> float:
        return self.japan_repatriation + self.treasury_forced_sales + self.supply_term_premium

    @property
    def net_upward(self) -> float:
        return self.upward - self.downward

    def signed_result(self) -> YieldSign | None:
        # No physical unit or response coefficients admitted -> no empirical sign.
        if not self.common_basis_receipt:
            return None
        if self.net_upward > 0:
            return YieldSign.UP
        if self.net_upward < 0:
            return YieldSign.DOWN
        return YieldSign.FLAT


def rival_fixture_pair() -> tuple[OpposingFlows, OpposingFlows]:
    """Same JPY liquidation/repatriation inputs, opposite outcomes."""
    return (
        OpposingFlows(8, 2, 3, 2, 1, True),
        OpposingFlows(1, 1, 3, 2, 1, True),
    )


def sensitivity_to_haven(a: OpposingFlows, haven_values: tuple[float, ...]) -> tuple[YieldSign | None, ...]:
    return tuple(
        OpposingFlows(v, a.easing_expectation, a.japan_repatriation,
                      a.treasury_forced_sales, a.supply_term_premium,
                      a.common_basis_receipt).signed_result()
        for v in haven_values
    )
