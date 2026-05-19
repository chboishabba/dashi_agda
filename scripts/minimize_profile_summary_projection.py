#!/usr/bin/env python3
"""Find the weakest field projection that preserves profile-summary separation.

This script operates on the materialized artifact emitted by
`scripts/materialize_profile_summary_family.hs`. It reports:

- the smallest field subsets that separate both the full current taxonomy and
  the saturated-only slice; and
- the smallest field subsets that preserve the same equivalence classes as the
  full six-field family on both scopes.
"""

from __future__ import annotations

import itertools
import json
from pathlib import Path


ARTIFACT = Path("artifacts/hecke/profile_summary_family.json")
FIELDS = (
    "forcedStableCount",
    "motifChangeCount",
    "totalDrift",
    "repatterningCount",
    "contractiveCount",
    "expansiveCount",
)
ALL_GENERATORS = (
    "explicitWidth1",
    "explicitWidth2",
    "explicitWidth3",
    "balancedCycle",
    "denseComposed",
    "balancedComposed",
    "anchoredTrajectory",
    "supportCascade",
    "fullSupportCascade",
)
SATURATED_GENERATORS = (
    "explicitWidth2",
    "explicitWidth3",
    "balancedCycle",
    "denseComposed",
    "balancedComposed",
    "anchoredTrajectory",
    "supportCascade",
    "fullSupportCascade",
)


def load_artifact() -> dict[str, list[dict[str, int]]]:
    return json.loads(ARTIFACT.read_text(encoding="utf-8"))


def encode(
    artifact: dict[str, list[dict[str, int]]],
    names: tuple[str, ...],
    fields: tuple[str, ...],
) -> dict[str, tuple[tuple[int, ...], ...]]:
    return {
        name: tuple(tuple(lane[field] for field in fields) for lane in artifact[name])
        for name in names
    }


def partition(encoded: dict[str, tuple[tuple[int, ...], ...]]) -> set[tuple[str, ...]]:
    groups: dict[tuple[tuple[int, ...], ...], list[str]] = {}
    for name, value in encoded.items():
        groups.setdefault(value, []).append(name)
    return {tuple(sorted(group)) for group in groups.values()}


def minimal_subsets(predicate):
    for size in range(1, len(FIELDS) + 1):
        matches = [subset for subset in itertools.combinations(FIELDS, size) if predicate(subset)]
        if matches:
            return matches
    return []


def main() -> None:
    artifact = load_artifact()
    full_all_partition = partition(encode(artifact, ALL_GENERATORS, FIELDS))
    full_saturated_partition = partition(encode(artifact, SATURATED_GENERATORS, FIELDS))

    separating = minimal_subsets(
        lambda subset: len(partition(encode(artifact, ALL_GENERATORS, subset))) > 1
        and len(partition(encode(artifact, SATURATED_GENERATORS, subset))) > 1
    )

    partition_preserving = minimal_subsets(
        lambda subset: partition(encode(artifact, ALL_GENERATORS, subset)) == full_all_partition
        and partition(encode(artifact, SATURATED_GENERATORS, subset)) == full_saturated_partition
    )

    print(
        json.dumps(
            {
                "artifact": str(ARTIFACT),
                "minimal_separating_subsets": separating,
                "minimal_partition_preserving_subsets": partition_preserving,
                "full_all_partition": sorted(full_all_partition),
                "full_saturated_partition": sorted(full_saturated_partition),
            },
            indent=2,
            sort_keys=True,
        )
    )


if __name__ == "__main__":
    main()
