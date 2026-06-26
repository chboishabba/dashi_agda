from __future__ import annotations

import json
import subprocess
import sys
import textwrap
from pathlib import Path

import pytest


REPO_ROOT = Path(__file__).resolve().parents[1]
SCRIPT = REPO_ROOT / "scripts" / "repo_index.py"


def run_repo_index(root: Path, *args: str) -> dict[str, object]:
    result = subprocess.run(
        [sys.executable, str(SCRIPT), "--root", str(root), "--json", *args],
        cwd=REPO_ROOT,
        check=True,
        text=True,
        capture_output=True,
    )
    return json.loads(result.stdout)


@pytest.fixture()
def fixture_repo(tmp_path: Path) -> Path:
    files = {
        "DASHI/Interop/PNFSpectralNumericABICore.agda": """
            module DASHI.Interop.PNFSpectralNumericABICore where

            data NumericWitness : Set where
              witness : NumericWitness
        """,
        "DASHI/Interop/PNFSpectralVectorIndex.agda": """
            module DASHI.Interop.PNFSpectralVectorIndex where

            data VectorIndexWitness : Set where
              vectorWitness : VectorIndexWitness
        """,
        "DASHI/Interop/PNFSpectralCoordinateRebuildability.agda": """
            module DASHI.Interop.PNFSpectralCoordinateRebuildability where

            data CoordinateWitness : Set where
              coordinateWitness : CoordinateWitness
        """,
        "DASHI/Interop/PNFSpectralPhiPsiABICore.agda": """
            module DASHI.Interop.PNFSpectralPhiPsiABICore where

            import DASHI.Interop.PNFSpectralNumericABICore
            import DASHI.Interop.PNFSpectralVectorIndex
            import DASHI.Interop.PNFSpectralCoordinateRebuildability

            -- candidate-only
            data PNFPhiPsiABIStatus : Set where
              mkPNFPhiPsiABIStatus : PNFPhiPsiABIStatus

            data PsiProposalKind : Set where
              psiProposalKind : PsiProposalKind

            -- nearby comment for field extraction
            record PhiCoordinateTable : Set where
              field
                psiKind : PsiProposalKind
        """,
        "DASHI/Interop/BettiQiAdapter.agda": """
            module DASHI.Interop.BettiQiAdapter where

            import DASHI.Interop.PNFSpectralPhiPsiABICore

            -- candidate-only
            data BettiQiBridgeStatus : Set where
              mkBettiQiBridgeStatus : BettiQiBridgeStatus
        """,
        "Docs/support/reference/RepoGuide.md": """
            # Repo Guide

            Mention DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind here.
        """,
    }
    for rel_path, content in files.items():
        path = tmp_path / rel_path
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(textwrap.dedent(content).strip() + "\n", encoding="utf-8")
    return tmp_path


@pytest.fixture()
def built_index_path(fixture_repo: Path) -> Path:
    index_path = fixture_repo / ".repo-index" / "index.sqlite3"
    payload = run_repo_index(fixture_repo, "--index", str(index_path), "build")
    assert payload["schema_version"] == "2.0.0"
    assert payload["command"] == "build"
    assert payload["status"] == "written"
    assert index_path.exists()
    return index_path


def test_build_and_defs_work(built_index_path: Path, fixture_repo: Path) -> None:
    payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "defs",
        "DASHI.Interop.PNFSpectralPhiPsiABICore",
    )
    assert payload["schema_version"] == "2.0.0"
    match_ids = {item["symbol_id"] for item in payload["matches"]}
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore" in match_ids


def test_complete_status_requirements_refs_hover_and_graph(built_index_path: Path, fixture_repo: Path) -> None:
    complete_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "complete",
        "DASHI.Interop.PNF",
    )
    complete_ids = {item["symbol_id"] for item in complete_payload["matches"]}
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore" in complete_ids
    assert "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind" in complete_ids

    status_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "status",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PNFPhiPsiABIStatus",
    )
    assert status_payload["matches"][0]["status"]["promotion"] == "candidate-only"

    betti_status = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "status",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    assert betti_status["matches"][0]["status"]["promotion"] == "candidate-only"

    reqs_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
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
        fixture_repo,
        "--index",
        str(built_index_path),
        "refs",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PsiProposalKind",
    )
    assert any(item["ref_kind"] == "definition-use" for item in refs_payload["matches"])

    hover_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "hover",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    hover_match = hover_payload["matches"][0]
    assert hover_match["kind"] == "data"

    graph_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "graph",
        "DASHI.Interop.PNFSpectralPhiPsiABICore.PhiCoordinateTable",
    )
    outgoing = graph_payload["matches"][0]["outgoing"]
    assert any(node.get("symbol_id") == "DASHI.Interop.PNFSpectralNumericABICore" for node in outgoing)


def test_update_check_stale_and_freshness(built_index_path: Path, fixture_repo: Path) -> None:
    target = fixture_repo / "DASHI/Interop/BettiQiAdapter.agda"
    target.write_text(
        textwrap.dedent(
            """
            module DASHI.Interop.BettiQiAdapter where

            import DASHI.Interop.PNFSpectralPhiPsiABICore

            -- promoted true
            data BettiQiBridgeStatus : Set where
              mkBettiQiBridgeStatus : BettiQiBridgeStatus
            """
        ).strip()
        + "\n",
        encoding="utf-8",
    )

    stale_payload = run_repo_index(fixture_repo, "--index", str(built_index_path), "check-stale")
    stale_paths = {item["path"]: item["state"] for item in stale_payload["matches"]}
    assert stale_paths["DASHI/Interop/BettiQiAdapter.agda"] == "stale"

    defs_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "--check",
        "defs",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    freshness = defs_payload["freshness"]["DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus"]
    assert freshness["state"] == "stale"

    update_payload = run_repo_index(fixture_repo, "--index", str(built_index_path), "update")
    assert update_payload["command"] == "update"
    assert update_payload["parsed"] >= 1

    status_payload = run_repo_index(
        fixture_repo,
        "--index",
        str(built_index_path),
        "status",
        "DASHI.Interop.BettiQiAdapter.BettiQiBridgeStatus",
    )
    assert status_payload["matches"][0]["status"]["promotion"] == "promoted"


def test_progress_flag_is_safe_on_small_build(fixture_repo: Path, tmp_path: Path) -> None:
    index_path = tmp_path / "progress.sqlite3"
    payload = run_repo_index(
        fixture_repo,
        "--index",
        str(index_path),
        "--progress",
        "--jobs",
        "2",
        "--commit-every",
        "2",
        "build",
    )
    assert payload["status"] == "written"
