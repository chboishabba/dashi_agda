import json
from pathlib import Path

from agda_preflight.narrative_cache import NarrativeCache


def test_narrative_cache_finds_pr_and_commit_context_and_reports_coverage(tmp_path: Path):
    cache_path = tmp_path / ".repo-index" / "narrative.json"
    cache_path.parent.mkdir(parents=True)
    cache_path.write_text(
        json.dumps({
            "schema": "dashi.repo-narrative.v1",
            "authority": "development-narrative",
            "source_status": {"git_commits": 2, "semantic_history_linked": True},
            "events": [
                {
                    "event_id": "commit:a",
                    "timestamp": 1,
                    "kind": "commit",
                    "title": "Recover Balaban spatial C3",
                    "text": "Recovered literal spatial C3 action.",
                    "touched_objects": ["DASHI.Physics.BalabanSpatialC3"],
                    "introduced_objects": [],
                    "removed_objects": [],
                }
            ],
        }),
        encoding="utf-8",
    )
    cache = NarrativeCache(tmp_path)
    result = cache.search("Balaban C3")
    assert result["available"] is True
    assert result["matches"]
    assert result["matches"][0]["event_id"] == "commit:a"
    assert result["authority"] == "development-narrative"


def test_narrative_cache_missing_is_incomplete_not_empty(tmp_path: Path):
    result = NarrativeCache(tmp_path).search("anything")
    assert result["available"] is False
    assert result["complete"] is False
    assert result["matches"] == []
