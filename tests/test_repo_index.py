from __future__ import annotations

import json
import subprocess
import sys
from pathlib import Path
from typing import Iterator

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "repo_index.py"


def run_repo_index(*args: str) -> dict[str, object]:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(REPO_ROOT), "--json", *args],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    return json.loads(result.stdout)


@pytest.fixture(scope="module")
def built_index_path(tmp_path_factory: pytest.TempPathFactory) -> Iterator[Path]:
    index_path = tmp_path_factory.mktemp("repo-index") / "index.json"
    payload = run_repo_index("--index", str(index_path), "build")
    assert payload["schema_version"] == "1.1.0"
    assert payload["command"] == "build"
    assert payload["status"] == "written"
    assert index_path.exists()
    yield index_path


def test_build_writes_versioned_index(built_index_path: Path) -> None:
    index_path = built_index_path
    data = json.loads(index_path.read_text(encoding="utf-8"))
    assert data["schema_version"] == "1.1.0"
    assert data["symbols"]
    assert data["references"] == []


def test_rebuild_reuses_an_existing_index(built_index_path: Path) -> None:
    index_path = built_index_path
    payload = run_repo_index("--index", str(index_path), "build")
    assert payload["schema_version"] == "1.1.0"
    assert payload["status"] == "written"


def test_defs_and_complete_cover_the_named_agda_surfaces(built_index_path: Path) -> None:
    index_path = built_index_path

    defs_payload = run_repo_index(
        "--index",
        str(index_path),
        "defs",
        "DASHI.Interop.PNFSpectralPhiPsiABICore",
    )
    match_ids = {item["symbol_id"] for item in defs_payload["matches"]}
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore" in match_ids

    complete_payload = run_repo_index("--index", str(index_path), "complete", "DASHI.Interop.PNF")
    complete_ids = {item["symbol_id"] for item in complete_payload["matches"]}
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore" in complete_ids
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind" in complete_ids

    betti_defs = run_repo_index(
        "--index",
        str(index_path),
        "defs",
        "DASHI.Interop.BettiQiAdapter",
    )
    betti_ids = {item["symbol_id"] for item in betti_defs["matches"]}
    assert "DASHI.Interop.BettiQiAdapter" in betti_ids


def test_status_requirements_refs_hover_and_graph(built_index_path: Path) -> None:
    index_path = built_index_path

    status_payload = run_repo_index(
        "--index",
        str(index_path),
        "status",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PNFPhiPsiABIStatus",
    )
    assert status_payload["matches"][0]["status"]["promotion"] == "candidate-only"

    betti_status = run_repo_index(
        "--index",
        str(index_path),
        "status",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    assert betti_status["matches"][0]["status"]["promotion"] == "candidate-only"

    reqs_payload = run_repo_index(
        "--index",
        str(index_path),
        "reqs",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PhiCoordinateTable",
    )
    syntactic = reqs_payload["matches"][0]["requirements"]["syntactic_requirements"]
    imported = {item["symbol"] for item in syntactic if item["kind"] == "import"}
    assert {
        "DASHI.Interop.PNFSpectralNumericABICore",
        "DASHI.Interop.PNFSpectralVectorIndex",
        "DASHI.Interop.PNFSpectralCoordinateRebuildability",
    }.issubset(imported)

    refs_payload = run_repo_index(
        "--index",
        str(index_path),
        "refs",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind",
    )
    assert any(item["ref_kind"] == "definition-use" for item in refs_payload["matches"])

    hover_payload = run_repo_index(
        "--index",
        str(index_path),
        "hover",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    hover_match = hover_payload["matches"][0]
    assert hover_match["kind"] == "data"
    assert "BettiQiBridgeStatus" in hover_match["symbol_id"]

    graph_payload = run_repo_index(
        "--index",
        str(index_path),
        "graph",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PhiCoordinateTable",
    )
    graph_node = graph_payload["matches"][0]
    outgoing = graph_node["outgoing"]
    assert outgoing
    assert any(node.get("symbol_id") == "DASHI.Interop.PNFSpectralNumericABICore" for node in outgoing)
