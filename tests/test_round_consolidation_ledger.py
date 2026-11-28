import json
from pathlib import Path

from scripts.round_consolidation_ledger import build_ledger, is_historical_round_module, validate_mapping, _build_scoped_index
from scripts.round_migration_worklist import build_worklist
from scripts.round_migration_lifecycle import _probe_summary
from scripts.round_migration_candidates import build_report
from scripts.round_migration_bundle_plan import build_plan
from scripts.round_migration_roadmap import build_roadmap


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


def test_migration_worklist_groups_reverse_cone_consumers_without_mapping_them():
    ledger = {
        "repo_root": "/repo",
        "terminal_recipients": ["DASHI.CanonicalClay"],
        "modules": [
            {
                "module": "DASHI.Round7Exact",
                "terminal_recipient_candidates": ["DASHI.CanonicalClay"],
                "preferred_canonical_targets": [],
                "reverse_cone_nonhistorical_consumers": ["DASHI.LiveConsumer"],
                "nonhistorical_importers": ["DASHI.LiveConsumer"],
            },
            {
                "module": "DASHI.Round8Exact",
                "terminal_recipient_candidates": ["DASHI.CanonicalClay"],
                "preferred_canonical_targets": [],
                "reverse_cone_nonhistorical_consumers": ["DASHI.LiveConsumer"],
                "nonhistorical_importers": [],
            },
        ],
    }
    worklist = build_worklist(ledger)
    assert worklist["live_consumer_count"] == 1
    row = worklist["rows"][0]
    assert row["historical_module_count"] == 2
    assert row["direct_historical_imports"] == ["DASHI.Round7Exact"]
    assert row["reverse_cone_only"] == ["DASHI.Round8Exact"]
    assert row["review_status"] == "needs-semantic-review"
    assert row["ranked_canonical_candidates"][0]["module"] == "DASHI.CanonicalClay"


def test_probe_summary_keeps_batch_pass_distinct_from_authorization():
    summary = _probe_summary({
        "schema_version": 2,
        "receipts": [{"consumer": "DASHI.Live", "status": "probe-pass"}],
        "deletion_authorized": False,
    })
    assert summary == {"DASHI.Live": "batch-probe-pass"}
    assert _probe_summary({
        "receipts": [
            {"consumer": "DASHI.Live", "status": "probe-pass"},
            {"consumer": "DASHI.Live", "status": "probe-fail"},
        ]
    })["DASHI.Live"] == "probe-failed-or-incomplete"


def test_candidate_generator_rejects_generic_and_empty_hash_evidence(tmp_path):
    source = tmp_path / "packages.jsonl"
    packages = [
        {
            "package_id": "exact",
            "archive_status": "SUPERSEDED_EXACT",
            "selected_canonical_owner": "DASHI.CanonicalClay",
            "nonround_matches": [{
                "module": "DASHI.CanonicalClay", "name": "canonicalThing",
                "signature_sha256": "sig", "body_sha256": "body",
                "symbol_id": "DASHI.CanonicalClay.canonicalThing",
            }],
            "declarations": [{
                "module": "DASHI.Round1Exact", "name": "oldThing",
                "signature_sha256": "sig", "body_sha256": "body",
                "symbol_id": "DASHI.Round1Exact.oldThing",
            }],
        },
        {
            "package_id": "generic",
            "nonround_matches": [{
                "module": "DASHI.Other", "name": "proofLevel",
                "signature_sha256": "same", "body_sha256": "a",
            }, {
                "module": "DASHI.Other2", "name": "proofLevel2",
                "signature_sha256": "same", "body_sha256": "b",
            }],
            "declarations": [{
                "module": "DASHI.Round2Exact", "name": "generic",
                "signature_sha256": "same", "body_sha256": "",
            }],
        },
    ]
    source.write_text("\n".join(json.dumps(row) for row in packages) + "\n")
    report = build_report(source)
    assert report["status_counts"] == {"exact-selected-owner": 1, "signature-only": 1}
    assert report["mapping_candidate_count"] == 1
    assert report["mapping_candidates"][0]["target"] == "DASHI.CanonicalClay.canonicalThing"


def test_candidate_generator_groups_repeated_ambiguous_evidence(tmp_path):
    source = tmp_path / "packages.jsonl"
    match = {
        "module": "DASHI.CanonicalA", "name": "proofA",
        "signature_sha256": "sig", "body_sha256": "body",
    }
    rows = []
    for number in (1, 2):
        rows.append({
            "package_id": str(number),
            "nonround_matches": [match, {
                "module": "DASHI.CanonicalB", "name": "proofB",
                "signature_sha256": "sig", "body_sha256": "body",
            }],
            "declarations": [{
                "module": f"DASHI.Round{number}Exact", "name": "old",
                "signature_sha256": "sig", "body_sha256": "body",
            }],
        })
    source.write_text("\n".join(json.dumps(row) for row in rows) + "\n")
    report = build_report(source)
    assert report["status_counts"] == {"exact-ambiguous": 2}
    assert report["review_group_count"] == 1
    assert report["review_groups"][0]["declaration_count"] == 2


def test_live_bundle_plan_records_semantic_actions():
    report = build_plan(
        ROOT,
        json.loads((ROOT / ".dashi/round-stranded/ym-migration-candidates.json").read_text()),
        build_ledger(
            ROOT,
            ROOT / ".dashi/round-stranded/ym-packages.jsonl",
            ROOT / "Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json",
        ),
        json.loads((ROOT / ".dashi/round-stranded/ym-migration-plan.json").read_text()),
    )
    assert report["schema_version"] == 2
    assert report["declaration_count"] == 6
    assert all(bundle["semantic_actions_complete"] for bundle in report["bundles"])
    actions = {
        declaration["name"]: declaration["migration_action"]
        for bundle in report["bundles"]
        for declaration in bundle["declarations"]
    }
    assert actions["continuumYM"].startswith("retain-as-field")
    assert actions["literalClaySolutionFromTopDownThree"].startswith("inline-into-route-s")


def test_migration_roadmap_separates_filesystem_count_from_semantic_queue():
    base = ROOT / ".dashi/round-stranded"
    roadmap = build_roadmap(
        build_ledger(
            ROOT,
            ROOT / ".dashi/round-stranded/ym-packages.jsonl",
            ROOT / "Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json",
        ),
        json.loads((base / "ym-migration-plan.json").read_text()),
        json.loads((base / "ym-migration-candidates.json").read_text()),
        json.loads((base / "ym-live-bundle-plan.json").read_text()),
    )
    snapshot = roadmap["current_snapshot"]
    assert snapshot["historical_files_on_disk"] == build_ledger(
        ROOT,
        ROOT / ".dashi/round-stranded/ym-packages.jsonl",
        ROOT / "Docs/physics/YMClayEndpointPhaseLemmaManifest20261108.json",
    )["historical_module_count"]
    assert snapshot["live_declaration_uses"] == 12
    assert snapshot["source_bundles"] == 4
    assert snapshot["source_bearing_declarations"] == 6
    assert roadmap["deletion_gate"]["authorized"] is False
