import sqlite3
from pathlib import Path

from agda_preflight.narrative_cache import NarrativeCache, apply_narrative_gate
from agda_preflight.repository_store import (
    DEFAULT_REPOSITORY_DB,
    ensure_repository_schema,
    replace_narrative_events,
)


def test_narrative_cache_finds_pr_and_commit_context_and_reports_coverage(tmp_path: Path):
    database = tmp_path / DEFAULT_REPOSITORY_DB
    database.parent.mkdir(parents=True)
    conn = sqlite3.connect(database)
    conn.row_factory = sqlite3.Row
    ensure_repository_schema(conn)
    replace_narrative_events(
        conn,
        events=[
            {
                "event_id": "commit:a",
                "timestamp": 1,
                "kind": "commit",
                "title": "Recover Balaban spatial C3",
                "text": "Recovered literal spatial C3 action.",
                "touched_objects": ["DASHI.Physics.BalabanSpatialC3"],
                "introduced_objects": [],
                "removed_objects": [],
                "touched_paths": [],
                "authority": "development-narrative",
                "may_guide_discovery": True,
                "may_explain_intent": True,
                "may_establish_formal_fact": False,
                "may_establish_empirical_fact": False,
                "claimed_delta": ["Recovered literal spatial C3 action."],
                "frontier": [],
                "nonclaims": [],
                "verification": [],
            }
        ],
        source_status={
            "git_commits": 2,
            "commit_history_complete": True,
            "semantic_history_linked": True,
        },
    )
    conn.close()

    result = NarrativeCache(tmp_path).search("Balaban C3")
    assert result["available"] is True
    assert result["complete"] is True
    assert result["matches"]
    assert result["matches"][0]["event_id"] == "commit:a"
    assert result["authority"] == "development-narrative"


def test_narrative_cache_missing_is_incomplete_not_empty(tmp_path: Path):
    result = NarrativeCache(tmp_path).search("anything")
    assert result["available"] is False
    assert result["complete"] is False
    assert result["matches"] == []


def test_absence_gate_blocks_when_archaeology_is_missing_or_incomplete():
    receipt = {
        "absence_claim_permitted": True,
        "absence_status": "confirmed_no_indexed_candidate",
        "coverage": {},
    }
    gated = apply_narrative_gate(
        receipt,
        {"available": False, "complete": False, "matches": [], "authority": "development-narrative"},
    )
    assert gated["absence_claim_permitted"] is False
    assert gated["absence_status"] == "search_incomplete"


def test_absence_gate_blocks_when_history_contains_related_context():
    receipt = {
        "absence_claim_permitted": True,
        "absence_status": "confirmed_no_indexed_candidate",
        "coverage": {},
    }
    gated = apply_narrative_gate(
        receipt,
        {
            "available": True,
            "complete": True,
            "matches": [{"event_id": "pr:7", "title": "Historical candidate"}],
            "authority": "development-narrative",
        },
    )
    assert gated["absence_claim_permitted"] is False
    assert gated["absence_status"] == "historical_narrative_candidate_exists"


def test_absence_gate_preserves_confirmed_absence_only_when_archaeology_is_complete_and_empty():
    receipt = {
        "absence_claim_permitted": True,
        "absence_status": "confirmed_no_indexed_candidate",
        "coverage": {},
    }
    gated = apply_narrative_gate(
        receipt,
        {"available": True, "complete": True, "matches": [], "authority": "development-narrative"},
    )
    assert gated["absence_claim_permitted"] is True
    assert gated["absence_status"] == "confirmed_no_indexed_candidate"
