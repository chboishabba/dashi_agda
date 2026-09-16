from __future__ import annotations

import json
from dataclasses import asdict, dataclass


@dataclass(frozen=True)
class PositiveCorrelationReceipt:
    observed_integer: int
    left_role: str
    right_role: str
    strength: str
    same_integer_paid: bool
    independent_derivations: bool
    monster_context_shared: bool
    same_monster_class: bool
    same_source_family: bool
    positive_bridge_signal: bool
    same_object_paid: bool
    same_representation_paid: bool
    same_character_role_paid: bool
    theorem_authority_paid: bool
    next_bridge_search: str


CORRELATIONS: dict[int, PositiveCorrelationReceipt] = {
    17496: PositiveCorrelationReceipt(
        observed_integer=17496,
        left_role="OEIS A058678 / Monster class-42d McKay-Thompson coefficient",
        right_role="source-paid N(3B) restriction constituent degree 2*729*12",
        strength="crossContextNumericalEcho",
        same_integer_paid=True,
        independent_derivations=True,
        monster_context_shared=True,
        same_monster_class=False,
        same_source_family=False,
        positive_bridge_signal=True,
        same_object_paid=False,
        same_representation_paid=False,
        same_character_role_paid=False,
        theorem_authority_paid=False,
        next_bridge_search=(
            "inspect whether the 42d graded-trace coefficient and the N(3B) "
            "restriction degree factor through a shared Monster character, "
            "power-map, induction/restriction, or graded-module construction"
        ),
    ),
    32772: PositiveCorrelationReceipt(
        observed_integer=32772,
        left_role="OEIS A007255 / normalized Monster class-6B q^6 coefficient",
        right_role="independently derived weight-two C6 eigenspace multiplicity m1=m5",
        strength="sameClassCrossRoleEcho",
        same_integer_paid=True,
        independent_derivations=True,
        monster_context_shared=True,
        same_monster_class=True,
        same_source_family=True,
        positive_bridge_signal=True,
        same_object_paid=False,
        same_representation_paid=False,
        same_character_role_paid=False,
        theorem_authority_paid=False,
        next_bridge_search=(
            "inspect the 6B McKay-Thompson graded trace against the weight-two "
            "C6 Fourier decomposition, power maps, and eigenvalue multiplicity "
            "generating functions before introducing any same-object claim"
        ),
    ),
}


def _priority_key(receipt: PositiveCorrelationReceipt) -> tuple[int, int, int]:
    # Higher tuple wins.  This is a search-order heuristic only, not evidence weight.
    return (
        int(receipt.same_monster_class),
        int(receipt.same_source_family),
        int(receipt.monster_context_shared),
    )


def bridge_search_priority() -> tuple[PositiveCorrelationReceipt, ...]:
    return tuple(sorted(CORRELATIONS.values(), key=_priority_key, reverse=True))


def build_report() -> dict[str, object]:
    ordered = bridge_search_priority()
    return {
        "schema": "monster369-positive-correlation-runtime-v1",
        "positive_correlations": {
            str(integer): asdict(receipt)
            for integer, receipt in sorted(CORRELATIONS.items())
        },
        "bridge_search_priority": [item.observed_integer for item in ordered],
        "priority_semantics": (
            "search ordering only; same-class/source-family overlap is a reason to inspect a bridge sooner, "
            "not a probability, theorem score, or same-object promotion"
        ),
        "authority": {
            "positive_correlation_creates_same_object": False,
            "positive_correlation_creates_representation_theorem": False,
            "oeis_identity_creates_monster_action": False,
        },
    }


def main() -> int:
    print(json.dumps(build_report(), indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
