from __future__ import annotations

import importlib.util
import json
from pathlib import Path
import sqlite3
import sys

import pytest

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
        CREATE TABLE repo_symbols(
          symbol_id TEXT, file TEXT, name TEXT, module TEXT, kind TEXT
        );
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
        conn.execute(
            "INSERT INTO repo_file_imports VALUES (?, ?)", (path, imported)
        )
    return path


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


def test_targets_include_all_nine_seed_families():
    cluster = _load("ym_cluster", SCRIPTS / "cluster_ym_round_packages.py")
    cfg = cluster.load_targets(ROOT / "config/ym-round-extraction-targets.json")
    assert len(cfg["seed_families"]) == 9
    assert "DASHI.Physics.YangMills.BalabanClayCanonicalBFrontier" in cfg["seed_families"]
    assert cfg["target_prefix"] == "DASHI.Physics.YangMills."


def test_cluster_filters_to_target_round_family_and_is_deterministic():
    cluster = _load("ym_cluster", SCRIPTS / "cluster_ym_round_packages.py")
    cfg = {
        "target_prefix": "DASHI.Physics.YangMills.",
        "seed_families": ["DASHI.Physics.YangMills.Foo"],
        "candidate_positive_names": ["openLeaf"],
        "status_count_names": [],
    }
    conn = _fixture_conn()
    r1 = "DASHI.Physics.YangMills.FooRound1Exact"
    r2 = "DASHI.Physics.YangMills.FooRound2Exact"
    _add_module(conn, r1)
    _add_module(conn, r2, [r1])
    _add_module(conn, "DASHI.Physics.YangMills.OtherRound3Exact")
    _add_module(conn, "DASHI.Physics.YangMills.Canonical")
    _add_decl(conn, r1, "openLeaf", "sig-a", "body-a")
    _add_decl(conn, r2, "openLeaf", "sig-a", "body-b")
    conn.commit()

    imports = {r2: {r1}}
    parents, children = cluster.build_round_graph(imports, {r1, r2})
    assert parents[r2] == {r1}
    assert children[r1] == {r2}

    first = cluster.cluster_packages(conn, cfg)
    second = cluster.cluster_packages(conn, cfg)
    assert first == second
    assert len(first) == 1
    assert first[0]["family"] == "DASHI.Physics.YangMills.Foo"
    assert first[0]["terminal_leaves"] == [r2]
    assert first[0]["ancestor_round_count"] == 2
    assert first[0]["candidate_names"] == ["openLeaf"]
    assert len(first[0]["package_id"]) == 20


def _cfg():
    return {
        "candidate_positive_names": ["positiveTransferGap", "openLeaf"],
        "status_count_names": ["sourceAttachmentCountIsEighteen"],
        "negative_name_terms": ["nogo", "firewall", "impossible"],
        "compiler_hints": {
            "positiveTransferGap": ["positiveTransferGapFromOS4"]
        },
        "canonical_owner_by_name": {
            "positiveTransferGap": "DASHI.Physics.YangMills.BalabanCanonicalPhysicalTransferGapObligationExact"
        },
    }


def _package(name="openLeaf", sig="s1", body="b1"):
    return {
        "package_id": "p1",
        "family": "DASHI.Physics.YangMills.Foo",
        "terminal_leaves": ["DASHI.Physics.YangMills.FooRound1Exact"],
        "round_modules": ["DASHI.Physics.YangMills.FooRound1Exact"],
        "ancestor_round_count": 1,
        "declarations": [
            {
                "name": name,
                "signature_sha256": sig,
                "body_sha256": body,
                "normalized_signature": f"TYPE:{sig}",
                "module": "DASHI.Physics.YangMills.FooRound1Exact",
                "symbol_id": "round:symbol",
            }
        ],
        "candidate_names": [name],
        "signature_hashes": [sig],
        "body_hashes": [body],
        "dependency_neighbors": [],
        "status_only_evidence": [],
        "negative_result_evidence": [],
        "source_locations": [],
    }


def _indexes(*decls):
    exact, sig, name, body = {}, {}, {}, {}
    for d in decls:
        exact.setdefault((d["signature_sha256"], d["body_sha256"]), []).append(d)
        sig.setdefault(d["signature_sha256"], []).append(d)
        name.setdefault(d["name"], []).append(d)
        body.setdefault(d["body_sha256"], []).append(d)
    return {"exact": exact, "sig": sig, "name": name, "body": body}


def _nonround(name="canonicalLeaf", sig="s1", body="b1"):
    return {
        "name": name,
        "signature_sha256": sig,
        "body_sha256": body,
        "normalized_signature": f"TYPE:{sig}",
        "module": "DASHI.Physics.YangMills.Canonical",
        "symbol_id": "canonical:symbol",
    }


def test_classification_superseded_exact():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(_package(), _indexes(_nonround()), _cfg())
    assert row["disposition"] == "SUPERSEDED_EXACT"
    assert row["nonround_matches"]


def test_classification_alternate_proof_same_name_same_signature():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(name="sameLeaf"),
        _indexes(_nonround(name="sameLeaf", body="different")),
        _cfg(),
    )
    assert row["disposition"] == "ALTERNATE_PROOF"


def test_classification_superseded_renamed_requires_signature_evidence():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(name="legacyLeaf"),
        _indexes(_nonround(name="newLeaf", body="different")),
        _cfg(),
    )
    assert row["disposition"] == "SUPERSEDED_RENAMED"
    assert "identical normalized signature" in " ".join(row["evidence"])


def test_classification_body_only_match_fails_closed():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(sig="legacy-sig", body="same-body"),
        _indexes(_nonround(sig="other-sig", body="same-body")),
        _cfg(),
    )
    assert row["disposition"] == "GENUINE_OPEN_OBLIGATION"
    assert not row["nonround_matches"]


def test_status_count_is_status_only():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(name="sourceAttachmentCountIsEighteen"), _indexes(), _cfg()
    )
    assert row["disposition"] == "STATUS_ONLY"
    assert row.get("selected_canonical_owner") is None


def test_negative_result_is_preserved():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(name="selectedSourceNoGo"), _indexes(), _cfg()
    )
    assert row["disposition"] == "NEGATIVE_RESULT"
    assert row["retained_negative_results"]


def test_canonical_compiler_exists_but_selected_premise_remains_open():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    indexes = _indexes(_nonround(name="positiveTransferGapFromOS4", sig="other", body="x"))
    row = classify.classify_package(
        _package(name="positiveTransferGap", sig="legacy", body="legacy"), indexes, _cfg()
    )
    assert row["disposition"] == "CANONICAL_COMPILER_EXISTS"
    assert row["unresolved_residuals"]


def test_unrecognized_nonpositive_package_is_unresolved():
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    row = classify.classify_package(
        _package(name="opaqueHistoricalCoordinate"), _indexes(), _cfg()
    )
    assert row["disposition"] == "UNRESOLVED"


def test_receipt_archive_status_mapping_and_deterministic_jsonl(tmp_path):
    classify = _load("ym_classify", SCRIPTS / "classify_ym_round_packages.py")
    rows = [
        {**_package("openLeaf"), "disposition": "GENUINE_OPEN_OBLIGATION", "evidence": [], "nonround_matches": [], "retained_negative_results": [], "unresolved_residuals": ["openLeaf"], "selected_canonical_owner": "Owner"},
        {**_package("sourceAttachmentCountIsEighteen"), "package_id": "p2", "disposition": "STATUS_ONLY", "evidence": [], "nonround_matches": [], "retained_negative_results": [], "unresolved_residuals": [], "selected_canonical_owner": None},
    ]
    out = tmp_path / "ym-packages.jsonl"
    classify.write_receipts(rows, out)
    first = out.read_bytes()
    classify.write_receipts(list(reversed(rows)), out)
    assert out.read_bytes() == first
    decoded = [json.loads(line) for line in out.read_text().splitlines()]
    assert decoded[0]["archive_status"] in {"EXTRACTED", "HISTORICAL-ONLY"}
    status = next(x for x in decoded if x["disposition"] == "STATUS_ONLY")
    assert status["archive_status"] == "HISTORICAL-ONLY"
    assert status["selected_canonical_owner"] is None


CANONICAL_MODULES = {
    "cmp109_owner": ROOT / "DASHI/Physics/YangMills/BalabanCMP109CanonicalSourceSemanticsObligationsExact.agda",
    "transfer_gap_owner": ROOT / "DASHI/Physics/YangMills/BalabanCanonicalPhysicalTransferGapObligationExact.agda",
    "r409_owner": ROOT / "DASHI/Physics/YangMills/BalabanCMP116CanonicalSelectedTermReplayExact.agda",
    "r429_owner": ROOT / "DASHI/Physics/YangMills/BalabanCMP116CanonicalTraceEntropyBudgetExact.agda",
    "canonical_clay_residual": ROOT / "DASHI/Physics/YangMills/YangMillsCanonicalClayResidualExact.agda",
    "extraction_receipt": ROOT / "DASHI/Physics/YangMills/YangMillsRoundExtractionReceiptExact.agda",
}


def _source(key):
    path = CANONICAL_MODULES[key]
    assert path.exists(), f"missing canonical owner {path}"
    text = path.read_text(encoding="utf-8")
    assert "Round" not in "\n".join(
        line for line in text.splitlines() if line.lstrip().startswith(("open import", "import"))
    )
    assert "clayPromotion = true" not in text
    assert "clayYangMillsPromoted = true" not in text
    return text


def test_cmp109_owner_exposes_residual_obligations_without_scheduler_state():
    text = _source("cmp109_owner")
    assert "generatedHistoryResponseProducer" in text
    assert "betaDifferenceDecomposition" in text
    assert "physicalCompositeD1ChainRule" in text
    assert "blocked" not in text and "open =" not in text


def test_transfer_gap_owner_reuses_existing_compiler_and_exposes_selected_premises():
    text = _source("transfer_gap_owner")
    assert "BalabanClayT5ClusteringToTransferGapExact" in text
    assert "positiveTransferGapFromOS4" in text
    assert "selectedOS4Interpretation" in text
    assert "selectedContinuumClustering" in text


def test_r409_owner_separates_provenance_replay_and_proof_equality():
    text = _source("r409_owner")
    assert "sourceTranscriptionReceipt" in text
    assert "executionReplayReceipt" in text
    assert "selectedTermIdentity" in text
    assert "proofBearingEquality" in text


def test_r429_owner_separates_compiler_analytic_and_source_payments():
    text = _source("r429_owner")
    assert "exactCompilerStructure" in text
    assert "quantitativeTraceEntropyBound" in text
    assert "sameObjectTraceAttachment" in text


def test_canonical_clay_residual_imports_four_nonround_owners_and_stays_false():
    text = _source("canonical_clay_residual")
    for module in [
        "BalabanCMP109CanonicalSourceSemanticsObligationsExact",
        "BalabanCanonicalPhysicalTransferGapObligationExact",
        "BalabanCMP116CanonicalSelectedTermReplayExact",
        "BalabanCMP116CanonicalTraceEntropyBudgetExact",
    ]:
        assert module in text
    assert "CMP109.CMP109CanonicalSourceSemanticsObligations" in text
    assert "TransferGap.SelectedPhysicalTransferGapObligation" in text
    assert "R409.CMP116CanonicalSelectedTermReplay" in text
    assert "R429.CMP116CanonicalTraceEntropyBudget" in text
    assert "clayYangMillsPromoted = false" in text
    assert "clayPromotion = false" in text


def test_extraction_receipt_preserves_nonauthority_and_negative_results():
    text = _source("extraction_receipt")
    assert "roundsAuthoritativeByDefault = false" in text
    assert "extractionCreatesTheoremTruth = false" in text
    assert "statusCountsAreClayPayments = false" in text
    assert "negativeResultsPreserved = true" in text
    assert "roundFilesArchivedOrDeleted = false" in text
    assert "clayPromotion = false" in text


def test_all_canonical_modules_have_no_holes_postulates_or_unsafe_options():
    for key in CANONICAL_MODULES:
        text = _source(key)
        assert "{!!}" not in text
        assert "postulate" not in text
        assert "--allow-unsolved-metas" not in text
        assert "{-# OPTIONS --safe #-}" in text
