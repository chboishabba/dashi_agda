from pathlib import Path

from scripts.round_consolidation_ledger import build_ledger, is_historical_round_module, validate_mapping, _build_scoped_index


ROOT = Path(__file__).resolve().parents[1]


def test_round_detection_is_conservative():
    assert is_historical_round_module("DASHI.Physics.YangMills.FooRound123Exact", Path("FooRound123Exact.agda"))
    assert is_historical_round_module("DASHI.Physics.YangMills.R578", Path("R578.agda"))
    assert not is_historical_round_module("DASHI.Physics.YangMills.CanonicalClay", Path("CanonicalClay.agda"))


def test_real_ledger_fails_closed_for_current_historical_modules():
    ledger = build_ledger(
        ROOT,
        ROOT / ".dashi/round-stranded/ym-packages.jsonl",
        ROOT / "Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json",
    )
    assert ledger["historical_module_count"] > 0
    assert ledger["blocked_module_count"] > 0
    assert ledger["safe_to_delete_count"] < ledger["historical_module_count"]
    assert "deletion_policy" in ledger
    assert ledger["migration_goal"].startswith("remove every historical")
    assert sum(ledger["migration_action_counts"].values()) == ledger["historical_module_count"]
    assert ledger["migration_action_counts"]["rewire-nonhistorical-consumers"] > 0
    assert ledger["migration_action_counts"]["delete-orphan-after-import-scan"] > 0
    assert ledger["migration_action_counts"]["rewire-umbrella-consumers"] > 0
    assert ledger["migration_action_counts"]["delete-historical-island-after-import-scan"] > 0
    assert all(
        "DASHI.Physics.YangMills.Everything" not in row["canonical_consumer_modules"]
        for row in ledger["modules"]
    )


def test_mapping_rejects_round_to_round_consolidation():
    index = _build_scoped_index(ROOT, ROOT / "DASHI/Physics/YangMills")
    errors = validate_mapping(
        {
            "DASHI.Physics.YangMills.YangMillsClayCriticalPathRound578Exact::criticalPathCompilerMachineChecked":
            "DASHI.Physics.YangMills.YangMillsClayCriticalPathRound572Exact::round572CriticalPathCompilerLevel"
        },
        index,
    )
    assert any("target must be non-Round" in error for error in errors)
