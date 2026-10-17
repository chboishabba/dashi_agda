import json
from pathlib import Path

from agda_preflight.source_index import SourceIndex


def _seed_module(index: SourceIndex, *, path: str, module_name: str, interface: dict) -> None:
    index.connection.execute(
        """
        INSERT OR REPLACE INTO modules(
            path, module_name, mtime_ns, size, source_sha256,
            api_base_sha256, api_fingerprint, public_imports_json,
            interface_json, dependency_fingerprint, diagnostics_json,
            top_diagnostic_json, top_fixable_diagnostic_json, updated_ns
        ) VALUES(?, ?, 0, 0, '', '', '', '[]', ?, '', '[]', '', '', 0)
        """,
        (path, module_name, json.dumps(interface)),
    )
    index.connection.commit()


def test_symbol_search_prefers_live_and_hides_history_by_default(tmp_path: Path):
    db = tmp_path / "index.sqlite3"
    with SourceIndex(tmp_path, db) as index:
        _seed_module(
            index,
            path="DASHI/Core/Foo.agda",
            module_name="DASHI.Core.Foo",
            interface={"functions": [{"name": "target", "type": "Nat → Nat"}]},
        )
        _seed_module(
            index,
            path="DASHI/Physics/Closure/FooRound2Exact.agda",
            module_name="DASHI.Physics.Closure.FooRound2Exact",
            interface={"functions": [{"name": "target", "type": "Nat → Nat"}]},
        )
        index.refresh_semantic_catalog()
        live = index.search_symbols("target")
        all_results = index.search_symbols("target", include_history=True)

    assert len(live) == 1
    assert live[0]["module_name"] == "DASHI.Core.Foo"
    assert len(all_results) == 2
    assert all_results[1]["surface_role"] == "historical_snapshot"


def test_related_symbols_stratifies_signature_equivalence_and_similarity(tmp_path: Path):
    db = tmp_path / "index.sqlite3"
    with SourceIndex(tmp_path, db) as index:
        _seed_module(
            index,
            path="DASHI/Core/Foo.agda",
            module_name="DASHI.Core.Foo",
            interface={"functions": [
                {"name": "target", "type": "(x : Nat) → Nat"},
                {"name": "sameShape", "type": "(y : Nat) → Nat"},
                {"name": "other", "type": "Bool → Bool"},
            ]},
        )
        index.refresh_semantic_catalog()
        report = index.related_symbols("DASHI.Core.Foo.target")

    assert report["query_symbol"]["name"] == "target"
    assert any(item["name"] == "sameShape" for item in report["signature_equivalent"])
    assert all("similarity" in item for item in report["similar"])


def test_discovery_without_repo_index_never_authorizes_absence(tmp_path: Path):
    db = tmp_path / "index.sqlite3"
    with SourceIndex(tmp_path, db) as index:
        _seed_module(
            index,
            path="DASHI/Core/Foo.agda",
            module_name="DASHI.Core.Foo",
            interface={"functions": [{"name": "knownThing", "type": "Nat"}]},
        )
        index.refresh_semantic_catalog()
        known = index.discovery_receipt("knownThing")
        fuzzy = index.discovery_receipt("known thing")
        missing = index.discovery_receipt("certainlyMissingSymbolXYZ")

    assert known["absence_claim_permitted"] is False
    assert known["live_matches"]
    assert fuzzy["absence_claim_permitted"] is False
    assert any(item["name"] == "knownThing" for item in fuzzy["query_similar"])
    assert missing["absence_claim_permitted"] is False
    assert missing["absence_status"] == "search_incomplete"
    assert missing["coverage"]["repo_index"]["state"] == "missing"


def test_absence_is_forbidden_when_repo_index_is_missing_even_if_preflight_db_has_no_match(tmp_path: Path):
    unindexed = tmp_path / "DASHI" / "Hidden.agda"
    unindexed.parent.mkdir(parents=True)
    unindexed.write_text("module DASHI.Hidden where\n", encoding="utf-8")
    db = tmp_path / "index.sqlite3"
    with SourceIndex(tmp_path, db) as index:
        receipt = index.discovery_receipt("missingObject")

    assert receipt["absence_claim_permitted"] is False
    assert receipt["absence_status"] == "search_incomplete"
    assert receipt["coverage"]["repo_index"]["complete"] is False
