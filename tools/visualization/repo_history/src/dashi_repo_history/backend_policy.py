from __future__ import annotations

from dataclasses import asdict, dataclass
from statistics import median
from typing import Any, Iterable


@dataclass(frozen=True)
class IncrementalStepTiming:
    commit: str
    parent: str
    changed_paths: int
    affected_modules: int
    plan_ns: int
    patch_ns: int
    total_ns: int
    removed_nodes: int
    added_nodes: int
    removed_edges: int
    added_edges: int
    updated_nodes: int = 0
    updated_edges: int = 0
    recomputed_nodes: int = 0
    recomputed_edges: int = 0

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


@dataclass(frozen=True)
class BackendDecisionPolicy:
    # Interactive/animation extraction should normally stay comfortably below
    # a frame-scale human latency boundary.
    patch_p95_ns_limit: int = 50_000_000  # 50 ms

    # If patching is a small fraction of the measured incremental hot path,
    # moving only that portion to Rust is unlikely to pay for FFI/build cost.
    patch_share_limit: float = 0.35
    planning_share_limit: float = 0.45
    planning_p95_ns_limit: int = 50_000_000  # 50 ms

    # A large affected-module set is a warning that the invalidation model, not
    # Python itself, may be the first thing to improve.
    affected_modules_p95_limit: int = 128

    min_samples_for_rust_decision: int = 50


@dataclass(frozen=True)
class BackendDecision:
    recommendation: str
    reason: str
    samples: int
    patch_p50_ns: int
    patch_p95_ns: int
    patch_share: float
    planning_p95_ns: int
    planning_share: float
    semantic_core_p95_ns: int
    semantic_core_share: float
    affected_modules_p95: int

    def to_dict(self) -> dict[str, Any]:
        return asdict(self)


def _percentile(values: list[int], fraction: float) -> int:
    if not values:
        return 0
    ordered = sorted(values)
    index = round((len(ordered) - 1) * fraction)
    return int(ordered[index])


def decide_backend(
    timings: Iterable[IncrementalStepTiming],
    policy: BackendDecisionPolicy | None = None,
) -> BackendDecision:
    policy = policy or BackendDecisionPolicy()
    timings = list(timings)

    if not timings:
        return BackendDecision(
            recommendation="python-reference",
            reason="no incremental timing samples yet",
            samples=0,
            patch_p50_ns=0,
            patch_p95_ns=0,
            patch_share=0.0,
            planning_p95_ns=0,
            planning_share=0.0,
            semantic_core_p95_ns=0,
            semantic_core_share=0.0,
            affected_modules_p95=0,
        )

    patch = [item.patch_ns for item in timings]
    planning = [item.plan_ns for item in timings]
    semantic_core = [
        item.plan_ns + item.patch_ns
        for item in timings
    ]
    total_patch = sum(patch)
    total_planning = sum(planning)
    total_core = sum(semantic_core)
    total = sum(item.total_ns for item in timings)
    affected = [item.affected_modules for item in timings]

    patch_p50 = int(median(patch))
    patch_p95 = _percentile(patch, 0.95)
    planning_p95 = _percentile(planning, 0.95)
    core_p95 = _percentile(semantic_core, 0.95)
    affected_p95 = _percentile(affected, 0.95)
    share = total_patch / max(1, total)
    planning_share = total_planning / max(1, total)
    core_share = total_core / max(1, total)

    if len(timings) < policy.min_samples_for_rust_decision:
        recommendation = "python-reference"
        reason = (
            "insufficient samples for a Rust migration decision; "
            "keep collecting profile receipts"
        )
    elif affected_p95 > policy.affected_modules_p95_limit:
        recommendation = "fix-invalidation-first"
        reason = (
            "affected-module fanout is high; improve semantic invalidation "
            "before changing implementation language"
        )
    elif (
        planning_p95 > policy.planning_p95_ns_limit
        and planning_share > policy.planning_share_limit
    ):
        recommendation = "persistent-index-first"
        reason = (
            "impact planning dominates; add/update a persistent resolution "
            "impact index before changing implementation language"
        )
    elif (
        patch_p95 > policy.patch_p95_ns_limit
        and share > policy.patch_share_limit
    ):
        recommendation = "rust-core-candidate"
        reason = (
            "Python semantic patching exceeds both p95 latency and measured "
            "hot-path share gates"
        )
    else:
        recommendation = "python-reference"
        reason = (
            "Python patching is within the configured latency/share envelope"
        )

    return BackendDecision(
        recommendation=recommendation,
        reason=reason,
        samples=len(timings),
        patch_p50_ns=patch_p50,
        patch_p95_ns=patch_p95,
        patch_share=share,
        planning_p95_ns=planning_p95,
        planning_share=planning_share,
        semantic_core_p95_ns=core_p95,
        semantic_core_share=core_share,
        affected_modules_p95=affected_p95,
    )
