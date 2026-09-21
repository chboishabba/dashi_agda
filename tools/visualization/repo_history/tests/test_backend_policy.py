from dashi_repo_history.backend_policy import (
    BackendDecisionPolicy,
    IncrementalStepTiming,
    decide_backend,
)


def _timing(
    *,
    patch_ns: int,
    total_ns: int,
    affected_modules: int = 2,
):
    return IncrementalStepTiming(
        commit="c",
        parent="p",
        changed_paths=1,
        affected_modules=affected_modules,
        plan_ns=1,
        patch_ns=patch_ns,
        total_ns=total_ns,
        removed_nodes=1,
        added_nodes=1,
        removed_edges=1,
        added_edges=1,
    )


def test_small_sample_never_forces_rust():
    decision = decide_backend(
        [_timing(patch_ns=100_000_000, total_ns=120_000_000)]
    )
    assert decision.recommendation == "python-reference"


def test_high_invalidation_fanout_is_algorithm_problem_first():
    policy = BackendDecisionPolicy(
        min_samples_for_rust_decision=3,
        affected_modules_p95_limit=10,
    )
    timings = [
        _timing(
            patch_ns=100_000_000,
            total_ns=120_000_000,
            affected_modules=30,
        )
        for _ in range(3)
    ]
    decision = decide_backend(timings, policy)

    assert decision.recommendation == "fix-invalidation-first"


def test_rust_candidate_requires_latency_and_hot_path_share():
    policy = BackendDecisionPolicy(
        min_samples_for_rust_decision=3,
        patch_p95_ns_limit=50_000_000,
        patch_share_limit=0.35,
        affected_modules_p95_limit=100,
    )
    timings = [
        _timing(
            patch_ns=90_000_000,
            total_ns=120_000_000,
        )
        for _ in range(3)
    ]
    decision = decide_backend(timings, policy)

    assert decision.recommendation == "rust-core-candidate"


def test_python_stays_reference_when_patch_is_small_share():
    policy = BackendDecisionPolicy(
        min_samples_for_rust_decision=3,
        patch_p95_ns_limit=50_000_000,
        patch_share_limit=0.35,
    )
    timings = [
        _timing(
            patch_ns=60_000_000,
            total_ns=500_000_000,
        )
        for _ in range(3)
    ]
    decision = decide_backend(timings, policy)

    assert decision.recommendation == "python-reference"


def test_planning_hotspot_prefers_persistent_index_before_rust():
    policy = BackendDecisionPolicy(
        min_samples_for_rust_decision=3,
        planning_p95_ns_limit=50_000_000,
        planning_share_limit=0.45,
        patch_p95_ns_limit=50_000_000,
        patch_share_limit=0.35,
        affected_modules_p95_limit=100,
    )
    timings = [
        IncrementalStepTiming(
            commit=f"c{i}",
            parent="p",
            changed_paths=1,
            affected_modules=2,
            plan_ns=90_000_000,
            patch_ns=10_000_000,
            total_ns=120_000_000,
            removed_nodes=1,
            added_nodes=1,
            removed_edges=1,
            added_edges=1,
        )
        for i in range(3)
    ]

    decision = decide_backend(timings, policy)

    assert decision.recommendation == "persistent-index-first"
    assert decision.planning_share > decision.patch_share
