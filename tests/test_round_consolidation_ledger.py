import json
from pathlib import Path

from scripts.round_consolidation_ledger import build_ledger, is_historical_round_module, validate_mapping, _build_scoped_index
from scripts.round_migration_worklist import build_worklist
from scripts.round_migration_lifecycle import _probe_summary
from scripts.round_context_probe import apply_probed_batches
from scripts.round_migration_candidates import build_report
from scripts.round_migration_bundle_plan import build_plan
from scripts.round_migration_roadmap import build_roadmap
from scripts.round_migration_reconcile import build_reconciliation
from scripts.round_migration_repair import build_repair_plan, suggest_repairs


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
        json.loads((ROOT / ".dashi/round-stranded/ym-consolidation-ledger.json").read_text()),
        json.loads((ROOT / ".dashi/round-stranded/ym-migration-plan.json").read_text()),
    )
    assert report["schema_version"] == 3
    assert report["declaration_count"] == 6
    assert all(bundle["semantic_actions_complete"] for bundle in report["bundles"])
    assert report["shared_structural_bundle_count"] == 3
    assert report["shared_structural_declaration_count"] == 4
    structural = {
        bundle["historical_module"]: bundle
        for bundle in report["shared_structural_bundles"]
    }
    assert structural[
        "DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact"
    ]["recipient_status"] == "status-owner-review-required"
    assert structural[
        "DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact"
    ]["recipient_status"] == "recipient-review-required"
    assert structural[
        "DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact"
    ]["recipient_status"] == "recipient-review-required"
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
        json.loads((base / "ym-consolidation-ledger.json").read_text()),
        json.loads((base / "ym-migration-plan.json").read_text()),
        json.loads((base / "ym-migration-candidates.json").read_text()),
        json.loads((base / "ym-live-bundle-plan.json").read_text()),
    )
    snapshot = roadmap["current_snapshot"]
    assert snapshot["historical_files_on_disk"] == json.loads(
        (base / "ym-consolidation-ledger.json").read_text()
    )["historical_module_count"]
    assert snapshot["historical_files_on_disk"] > snapshot["source_bundles"]
    assert snapshot["live_declaration_uses"] == 12
    assert snapshot["source_bundles"] == 4
    assert snapshot["source_bearing_declarations"] == 6
    assert roadmap["deletion_gate"]["authorized"] is False


def test_reconciliation_consumes_bundle_and_metadata_actions_without_mapping_them():
    plan = {
        "status_counts": {"mapping-incomplete": 2, "unused-import-remove-or-recheck": 1},
        "rows": [
            {
                "consumer": "DASHI.Live",
                "consumer_path": "DASHI/Live.agda",
                "line": 7,
                "historical_module": "DASHI.RoundSource",
                "status": "mapping-incomplete",
                "used_names": ["bundleThing"],
            },
            {
                "consumer": "DASHI.Live",
                "consumer_path": "DASHI/Live.agda",
                "line": 8,
                "historical_module": "DASHI.RoundMeta",
                "status": "mapping-incomplete",
                "used_names": ["statusThing"],
            },
            {
                "consumer": "DASHI.Live",
                "consumer_path": "DASHI/Live.agda",
                "line": 9,
                "historical_module": "DASHI.RoundContext",
                "status": "unused-import-remove-or-recheck",
                "used_names": [],
            },
        ],
    }
    candidates = {
        "rows": [{
            "module": "DASHI.RoundMeta",
            "name": "statusThing",
            "migration_relevance": "live-declaration-use",
            "status": "exact-ambiguous",
        }],
    }
    bundles = {"bundles": [{
        "historical_module": "DASHI.RoundSource",
        "proposed_recipient": "DASHI.Canonical",
        "declarations": [{
            "name": "bundleThing",
            "migration_action": "inline",
        }],
    }]}
    report = build_reconciliation(
        ROOT, {}, plan, candidates, bundles,
        {"rows": []}, None,
    )
    assert report["declaration_action_counts"] == {
        "confirmed-bundle-migration": 1,
        "metadata-status-use": 1,
    }
    actions = {(row["historical_module"], row["action"]) for row in report["rows"]}
    assert ("DASHI.RoundSource", "semantic-action-confirmed") in actions
    assert ("DASHI.RoundMeta", "metadata-status-use") in actions
    assert ("DASHI.RoundContext", "context-probe-required") in actions


def test_reconciliation_keeps_unknown_used_names_as_semantic_gaps():
    report = build_reconciliation(
        ROOT, {}, {
            "rows": [{
                "consumer": "DASHI.Live",
                "consumer_path": "DASHI/Live.agda",
                "line": 7,
                "historical_module": "DASHI.RoundUnknown",
                "status": "mapping-incomplete",
                "used_names": ["unknownThing"],
            }],
        },
        {"rows": []}, {"bundles": []}, {"rows": []}, None,
    )
    assert report["action_counts"] == {"unresolved-semantic-mapping": 1}
    assert report["declaration_action_counts"] == {"unresolved-semantic-mapping": 1}


def test_reconciliation_marks_historical_rows_as_migration_or_mechanical_repair():
    report = build_reconciliation(
        ROOT, {}, {
            "rows": [{
                "consumer": "DASHI.Live",
                "consumer_path": "DASHI/Live.agda",
                "line": 7,
                "historical_module": "DASHI.RoundContext",
                "status": "unused-import-remove-or-recheck",
                "used_names": [],
            }],
        },
        {"rows": []}, {"bundles": []}, {"rows": []}, None,
    )
    row = report["rows"][0]
    assert row["scope"] == "historical-round-migration"
    assert row["queue"] == "mechanical-repair"
    assert row["blocking_for_migration"] is True
    assert report["queue_counts"] == {
        "mechanical-repair": 1,
        "migration-ready": 0,
        "proof-cone-external": 0,
    }


def test_repair_plan_is_dry_run_and_hash_bound(tmp_path):
    source = tmp_path / "Round170.agda"
    source.write_text("module Round170 where\n\npostulate\n  x : Set\n", encoding="utf-8")
    diagnostic = "[CoInfectiveImport] imported module is not safe"
    candidates = suggest_repairs(source, diagnostic)
    assert candidates == []

    source.write_text("{-# OPTIONS --safe #-}\nmodule Round170 where\n", encoding="utf-8")
    plan = build_repair_plan(tmp_path, "Round170.agda", diagnostic)
    assert plan["diagnostic_class"] == "unsafe-import-boundary"
    assert plan["queue"] == "mechanical-repair"
    assert plan["blocking_for_migration"] is True
    assert plan["requires_agda_receipt"] is True
    assert plan["proof_search_authorized"] is False
    assert plan["candidates"][0]["rule"] == "unsafe-boundary-remove-false-safe"


def test_repair_plan_routes_semantic_failures_outside_migration(tmp_path):
    source = tmp_path / "Canonical.agda"
    source.write_text("module Canonical where\n", encoding="utf-8")
    plan = build_repair_plan(tmp_path, "Canonical.agda", "Unequal terms")
    assert plan["queue"] == "proof-cone-external"
    assert plan["blocking_for_migration"] is False


def test_real_shared_round_interfaces_are_not_unresolved_theorem_mappings():
    report = json.loads(
        (ROOT / ".dashi/round-stranded/ym-migration-reconciliation.json").read_text()
    )
    rows = {
        (row["historical_module"], row["consumer"]): row
        for row in report["rows"]
        if row["historical_module"] in {
            "DASHI.Physics.YangMills.BalabanUnifiedPresentCutSchwingerRecoveryRound140Exact",
            "DASHI.Physics.YangMills.BalabanBetaDrivenCMP119ResidualFamilyRound219Exact",
            "DASHI.Physics.YangMills.BalabanFiniteVolumeReopeningPresentationRound283Exact",
        }
    }
    assert any(row["action"] == "metadata-status-use" for row in rows.values())
    assert any(row["action"] == "shared-bundle-migration" for row in rows.values())


def test_real_mapping_edges_already_classified_as_bookkeeping_are_not_probe_work():
    report = json.loads(
        (ROOT / ".dashi/round-stranded/ym-migration-reconciliation.json").read_text()
    )
    assert report["queue_counts"]["mechanical-repair"] == 391
    assert report["queue_counts"]["bookkeeping-context"] == 475
    assert report["action_counts"]["shared-bundle-migration"] == 154
    assert not any(
        row["action"] == "bookkeeping-context" and row["blocking_for_migration"]
        for row in report["rows"]
    )


def test_lifecycle_keeps_shared_bundle_review_distinct_from_mapping_gap():
    from scripts.round_migration_lifecycle import build_lifecycle
    lifecycle = build_lifecycle(
        {"historical_module_count": 3},
        {"rows": [{
            "consumer": "DASHI.Live",
            "consumer_path": "DASHI/Live.agda",
            "historical_module": "DASHI.RoundRecord",
            "used_names": ["SharedRecord"],
            "status": "mapping-incomplete",
        }]},
        reconciliation={"rows": [{
            "consumer": "DASHI.Live",
            "consumer_path": "DASHI/Live.agda",
            "historical_module": "DASHI.RoundRecord",
            "line": None,
            "action": "shared-bundle-migration",
            "declaration_actions": [],
        }]},
    )
    assert lifecycle["rows"][0]["lifecycle_state"] == "shared-bundle-recipient-review"


def test_probe_batch_apply_requires_matching_source_hash(tmp_path):
    target = tmp_path / "Live.agda"
    target.write_text("module Live where\nimport DASHI.RoundA\nimport DASHI.RoundB\n", encoding="utf-8")
    import hashlib
    source_hash = hashlib.sha256(target.read_bytes()).hexdigest()
    probe = {
        "receipts": [{
            "status": "probe-pass",
            "consumer_path": "Live.agda",
            "source_sha256": source_hash,
            "removed_imports": [{"historical_module": "DASHI.RoundA", "line": 2}],
        }],
    }
    applied = apply_probed_batches(tmp_path, probe, tmp_path / "checkpoints")
    assert applied[0]["status"] == "applied"
    assert "DASHI.RoundA" not in target.read_text(encoding="utf-8")
    assert "DASHI.RoundB" in target.read_text(encoding="utf-8")
    assert list((tmp_path / "checkpoints").iterdir())
