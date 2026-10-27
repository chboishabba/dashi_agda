from __future__ import annotations

import importlib.util
import sqlite3
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPTS = ROOT / "scripts"
sys.path.insert(0, str(SCRIPTS))


def _load(name: str, path: Path):
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec and spec.loader
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def _fixture_conn() -> sqlite3.Connection:
    conn = sqlite3.connect(":memory:")
    conn.row_factory = sqlite3.Row
    conn.executescript(
        """
        CREATE TABLE repo_files(path TEXT, module TEXT);
        CREATE TABLE repo_file_imports(file TEXT, imported_module TEXT);
        CREATE TABLE repo_symbols(symbol_id TEXT, file TEXT, name TEXT, module TEXT, kind TEXT);
        CREATE TABLE repo_symbol_signatures(
          symbol_id TEXT, normalized_signature TEXT,
          signature_sha256 TEXT, body_sha256 TEXT
        );
        """
    )
    return conn


def _add_module(conn, module: str, imports=()):
    path = module.replace(".", "/") + ".agda"
    conn.execute("INSERT INTO repo_files VALUES (?, ?)", (path, module))
    for imported in imports:
        conn.execute("INSERT INTO repo_file_imports VALUES (?, ?)", (path, imported))


def _add_decl(conn, module: str, name: str, sig: str, body: str):
    path = module.replace(".", "/") + ".agda"
    symbol_id = f"{module}:{name}:{sig}:{body}"
    conn.execute(
        "INSERT INTO repo_symbols VALUES (?, ?, ?, ?, 'signature')",
        (symbol_id, path, name, module),
    )
    conn.execute(
        "INSERT INTO repo_symbol_signatures VALUES (?, ?, ?, ?)",
        (symbol_id, f"TYPE:{sig}", sig, body),
    )


def _cfg():
    return {
        "schema_version": 1,
        "target_prefixes": ["DASHI.Physics.Closure.", "DASHI.Papers.NavierStokes."],
        "package_namespace": "ns-round-package",
        "candidate_positive_names": [],
        "status_count_names": ["statusCount"],
        "status_name_patterns": [
            r"IsFalse$",
            r"IsTrue$",
            r"CountIs",
            r"Regression",
            r"StillOpen$",
        ],
        "negative_name_terms": ["nogo"],
        "compiler_hints": {},
        "canonical_owner_by_name": {},
        "canonical_owner_by_family": {},
        "nonround_match_sample_limit": 10,
        "outputs": {"clusters": "x", "receipts": "y"},
    }


def test_ns_config_uses_two_prefixes_without_seed_families():
    engine = _load("round_engine", SCRIPTS / "_round_package_extraction.py")
    cfg = engine.load_targets(ROOT / "config/ns-round-extraction-targets.json")
    assert cfg["target_prefixes"] == [
        "DASHI.Physics.Closure.",
        "DASHI.Papers.NavierStokes.",
    ]
    assert "seed_families" not in cfg
    assert cfg["package_namespace"] == "ns-round-package"
    assert cfg["nonround_match_sample_limit"] == 10
    assert cfg["status_name_patterns"] == [
        "IsFalse$",
        "IsTrue$",
        "CountIs",
        "Regression",
        "StillOpen$",
    ]


def test_ns_discovers_round_families_under_both_prefixes_without_seeds():
    engine = _load("round_engine_multi", SCRIPTS / "_round_package_extraction.py")
    conn = _fixture_conn()
    a1 = "DASHI.Physics.Closure.AlphaRound1Exact"
    a2 = "DASHI.Physics.Closure.AlphaRound2Exact"
    b1 = "DASHI.Papers.NavierStokes.BetaRound1Exact"
    _add_module(conn, a1)
    _add_module(conn, a2, [a1])
    _add_module(conn, b1)
    _add_module(conn, "DASHI.Physics.YangMills.IgnoredRound1Exact")
    _add_decl(conn, a1, "alphaLeaf", "sa", "ba")
    _add_decl(conn, a2, "alphaLeaf", "sa", "bb")
    _add_decl(conn, b1, "betaLeaf", "sb", "bc")
    conn.commit()

    rows = engine.cluster_packages(conn, _cfg())
    assert {r["family"] for r in rows} == {
        "DASHI.Physics.Closure.Alpha",
        "DASHI.Papers.NavierStokes.Beta",
    }
    assert {r["domain"] for r in rows} == {
        "DASHI.Physics.Closure.",
        "DASHI.Papers.NavierStokes.",
    }
    assert len({r["package_id"] for r in rows}) == 2


def test_ns_package_ids_are_deterministic():
    engine = _load("round_engine_deterministic", SCRIPTS / "_round_package_extraction.py")
    conn = _fixture_conn()
    mod = "DASHI.Physics.Closure.GammaRound1Exact"
    _add_module(conn, mod)
    _add_decl(conn, mod, "gammaLeaf", "s", "b")
    conn.commit()
    first = engine.cluster_packages(conn, _cfg())
    second = engine.cluster_packages(conn, _cfg())
    assert first == second
    assert len(first[0]["package_id"]) == 20


def test_ns_body_only_match_fails_closed():
    engine = _load("round_engine_body", SCRIPTS / "_round_package_extraction.py")
    package = {
        "package_id": "p",
        "domain": "DASHI.Physics.Closure.",
        "family": "DASHI.Physics.Closure.Foo",
        "declarations": [{
            "symbol_id": "r", "name": "opaque", "module": "FooRound1Exact",
            "signature_sha256": "round-sig", "body_sha256": "same-body"
        }],
        "candidate_names": ["opaque"],
        "status_only_evidence": [],
        "negative_result_evidence": [],
    }
    indexes = {
        "exact": {},
        "sig": {},
        "name": {},
        "body": {"same-body": [{"symbol_id": "n"}]},
    }
    row = engine.classify_package(package, indexes, _cfg())
    assert row["disposition"] == "UNRESOLVED"
    assert row["nonround_match_count"] == 0


def test_ns_negative_and_status_receipts_are_preserved():
    engine = _load("round_engine_status", SCRIPTS / "_round_package_extraction.py")
    base = {
        "package_id": "p", "domain": "DASHI.Physics.Closure.",
        "family": "DASHI.Physics.Closure.Foo", "declarations": [],
        "status_only_evidence": [], "negative_result_evidence": [],
    }
    indexes = {"exact": {}, "sig": {}, "name": {}, "body": {}}
    status = engine.classify_package({**base, "candidate_names": ["statusCount"]}, indexes, _cfg())
    nogo = engine.classify_package({**base, "candidate_names": ["transportNoGo"]}, indexes, _cfg())
    assert status["disposition"] == "STATUS_ONLY"
    assert nogo["disposition"] == "NEGATIVE_RESULT"
    assert nogo["retained_negative_results"] == ["transportNoGo"]


def test_ns_status_patterns_reclassify_boolean_and_regression_receipts_only():
    engine = _load("round_engine_status_patterns", SCRIPTS / "_round_package_extraction.py")
    base = {
        "package_id": "p", "domain": "DASHI.Physics.Closure.",
        "family": "DASHI.Physics.Closure.Foo", "declarations": [],
        "status_only_evidence": [], "negative_result_evidence": [],
    }
    indexes = {"exact": {}, "sig": {}, "name": {}, "body": {}}
    for name in [
        "literalCarrierClosedIsFalse",
        "compilerClosedIsTrue",
        "sourceAttachmentCountIsEighteen",
        "strictMarginRegression",
        "physicalProducerStillOpen",
    ]:
        row = engine.classify_package({**base, "candidate_names": [name]}, indexes, _cfg())
        assert row["disposition"] == "STATUS_ONLY"
        assert row["selected_canonical_owner"] is None
    theorem = engine.classify_package(
        {**base, "candidate_names": ["integratedMixedHelicityBound"]}, indexes, _cfg()
    )
    assert theorem["disposition"] == "UNRESOLVED"


def test_ns_match_sampling_keeps_full_count_and_truncation_flag():
    engine = _load("round_engine_samples", SCRIPTS / "_round_package_extraction.py")
    package = {
        "package_id": "p", "domain": "DASHI.Physics.Closure.",
        "family": "DASHI.Physics.Closure.Foo",
        "candidate_names": ["opaque"], "status_only_evidence": [],
        "negative_result_evidence": [],
        "declarations": [{
            "symbol_id": "r", "name": "opaque", "module": "FooRound1Exact",
            "signature_sha256": "sig", "body_sha256": "round-body"
        }],
    }
    matches = [
        {"symbol_id": f"n{i}", "module": f"Canonical.M{i:02d}", "name": f"leaf{i}",
         "signature_sha256": "sig", "body_sha256": f"b{i}"}
        for i in range(24)
    ]
    indexes = {"exact": {}, "sig": {"sig": matches}, "name": {}, "body": {}}
    row = engine.classify_package(package, indexes, _cfg())
    assert row["disposition"] == "SUPERSEDED_RENAMED"
    assert row["nonround_match_count"] == 24
    assert len(row["nonround_matches"]) == 10
    assert row["nonround_matches_truncated"] is True


def test_ns_unresolved_has_no_fabricated_owner():
    engine = _load("round_engine_unresolved", SCRIPTS / "_round_package_extraction.py")
    package = {
        "package_id": "p", "domain": "DASHI.Physics.Closure.",
        "family": "DASHI.Physics.Closure.Foo", "declarations": [],
        "candidate_names": ["unknownLeaf"], "status_only_evidence": [],
        "negative_result_evidence": [],
    }
    indexes = {"exact": {}, "sig": {}, "name": {}, "body": {}}
    row = engine.classify_package(package, indexes, _cfg())
    assert row["disposition"] == "UNRESOLVED"
    assert row["selected_canonical_owner"] is None
    assert row["unresolved_residuals"] == ["unknownLeaf"]
