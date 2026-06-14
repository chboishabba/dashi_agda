from __future__ import annotations

import importlib.util
import json
import sys
from pathlib import Path
from types import ModuleType


REPO_ROOT = Path(__file__).resolve().parents[1]


def load_script(name: str) -> ModuleType:
    path = REPO_ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_publication_readiness_declares_core_agda_targets() -> None:
    readiness = load_script("check_publication_readiness")
    targets = {path.as_posix() for path in readiness.THEOREM_INTERFACE_TARGETS}
    assert {
        "DASHI/Papers/NavierStokes/TheoremInterface.agda",
        "DASHI/Papers/YangMills/TheoremInterface.agda",
        "DASHI/Papers/Unification/TheoremInterface.agda",
        "DASHI/Papers/CoreTheoremInterfaces.agda",
        "DASHI/Papers/VirtualPaper1Root.agda",
        "DASHI/Papers/VirtualPaper3Root.agda",
        "DASHI/Papers/VirtualPaper8Root.agda",
        "DASHI/DCHoTT/All.agda",
        "DASHI/Cubical/UnificationCandidate.agda",
    } <= targets


def test_publication_readiness_anchor_checks_pass_for_current_interfaces() -> None:
    readiness = load_script("check_publication_readiness")
    results = readiness.check_theorem_interfaces(REPO_ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []


def test_publication_readiness_tracks_paper_upgrade_obligations() -> None:
    readiness = load_script("check_publication_readiness")
    results = readiness.check_paper_upgrade_obligations(REPO_ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []


def test_publication_readiness_clay_publication_governance_is_fail_closed() -> None:
    readiness = load_script("check_publication_readiness")
    results = readiness.check_clay_publication_governance(REPO_ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []

    rows = readiness.CLAY_PUBLICATION_GOVERNANCE_ROWS
    gate_ids = {row["gate_id"] for row in rows}
    assert {
        "ARXIV_JOURNAL_READINESS_NOT_CLAY_PRIZE_SUBMISSION",
        "TWO_YEAR_COMMUNITY_ACCEPTANCE_EXTERNAL",
        "NO_DIRECT_CMI_MANUSCRIPT_SUBMISSION_CLAIM",
    } <= gate_ids
    assert all(row["governance_owner"] == "external" for row in rows)
    assert all(row["internal_readiness_promotes_clay"] is False for row in rows)
    assert all(row["clay_prize_submission_claim"] is False for row in rows)
    assert all(row["fail_closed"] is True for row in rows)


def test_publication_readiness_rejects_direct_cmi_submission_claim(tmp_path: Path) -> None:
    readiness = load_script("check_publication_readiness")
    draft = tmp_path / "Docs/papers/live/Paper3YangMillsClayDraft.md"
    draft.parent.mkdir(parents=True)
    draft.write_text(
        "We submitted the manuscript directly to Clay Mathematics Institute.\n",
        encoding="utf-8",
    )

    hits = readiness.forbidden_clay_publication_hits(
        tmp_path,
        [Path("Docs/papers/live/Paper3YangMillsClayDraft.md")],
    )

    assert hits
    assert "direct-cmi-manuscript-submission" in hits[0]


def test_publication_readiness_obligation_check_reports_missing_terms(tmp_path: Path) -> None:
    readiness = load_script("check_publication_readiness")
    paper1 = tmp_path / "Docs/papers/live/Paper1NavierStokesClayDraft.md"
    paper3 = tmp_path / "Docs/papers/live/Paper3YangMillsClayDraft.md"
    ledger = tmp_path / "Docs/support/live/PaperCommonCitationLedger.md"
    renderer = tmp_path / "scripts/render_core_paper_pdfs.py"
    for path in (paper1, paper3, ledger, renderer):
        path.parent.mkdir(parents=True, exist_ok=True)

    paper1.write_text(
        "Seregin/ESS intake and route compatible text, but no stationarity exponent.",
        encoding="utf-8",
    )
    paper3.write_text(
        "Balaban 1988 Lemma 3 activity bound, polymer summability, trace norm, Seiler compatibility.",
        encoding="utf-8",
    )
    ledger.write_text("", encoding="utf-8")
    renderer.write_text("", encoding="utf-8")

    results = readiness.check_paper_upgrade_obligations(tmp_path)
    failures = {result.name: result.detail for result in results if not result.ok}
    assert failures["paper1-ns-upgrade-obligations"] == "target-not-derived-r-1-12"
    assert failures["paper3-ym-upgrade-obligations"] == "option-b-deferred"


def test_core_paper_renderer_carries_balaban_upgrade_bib_note() -> None:
    renderer = load_script("render_core_paper_pdfs")
    bib = renderer.render_bib().lower()
    assert "balaban 1988 lemma 3 activity bound" in bib
    assert "polymer summability" in bib
    assert "trace norm transfer" in bib
    assert "option b deferred" in bib


def test_diagram_reproducibility_routes_cover_core_papers() -> None:
    diagrams = load_script("check_diagram_reproducibility")
    papers = {route.paper for route in diagrams.ROUTES}
    assert {"Paper1 NS", "Paper3 YM", "Paper8 Unification"} <= papers
    for route in diagrams.ROUTES:
        assert (REPO_ROOT / route.source).exists()
        assert route.command


def test_satellite_index_generator_writes_expected_lanes(tmp_path: Path) -> None:
    satellites = load_script("generate_satellite_paper_index")
    exit_code = satellites.main(["--repo-root", str(REPO_ROOT), "--out-dir", str(tmp_path)])
    assert exit_code == 0

    payload = json.loads((tmp_path / "satellite_paper_index.json").read_text(encoding="utf-8"))
    lanes = {row["lane"] for row in payload["rows"]}
    assert {
        "quantum/operator",
        "GR/DCHoTT",
        "DHR",
        "qualia/PNF",
        "diagnostic Yukawa/CKM",
    } == lanes
    assert all("no " in row["non_promotion_boundary"].lower() for row in payload["rows"])
