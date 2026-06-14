from __future__ import annotations

import importlib.util
import json
import sys
import textwrap
from pathlib import Path
from types import ModuleType


REPO_ROOT = Path(__file__).resolve().parents[1]
LIVE_CORE_PAPERS = {
    "paper1": REPO_ROOT / "Docs/papers/live/Paper1NavierStokesClayDraft.md",
    "paper3": REPO_ROOT / "Docs/papers/live/Paper3YangMillsClayDraft.md",
    "paper8": REPO_ROOT / "Docs/papers/live/Paper8UnificationDraft.md",
}


def load_script(name: str) -> ModuleType:
    path = REPO_ROOT / "scripts" / f"{name}.py"
    spec = importlib.util.spec_from_file_location(name, path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def read_live_paper(name: str) -> str:
    return LIVE_CORE_PAPERS[name].read_text(encoding="utf-8")


def squash(text: str) -> str:
    return " ".join(text.split())


def test_live_core_papers_have_real_author_and_no_internal_reference_placeholders() -> None:
    forbidden = {
        "pending final public author",
        "see common citation ledger",
        "citation ledger is for internal governance",
        "author: tbd",
    }

    for name, path in LIVE_CORE_PAPERS.items():
        text = path.read_text(encoding="utf-8")
        lower = text.lower()
        assert "Author: Johl Brown" in text, name
        assert all(phrase not in lower for phrase in forbidden), name


def test_live_paper1_records_seregin_ess_a32_as_fail_closed_intake() -> None:
    text = read_live_paper("paper1")
    lower = text.lower()

    assert "`Seregin2012`" in text
    assert "`ESS2003`" in text
    assert "`A3.2`" in text
    assert "Type-I blowup rescaling sequence" in text
    assert "ancient `L^{3,\\infty}` solution" in text
    assert "`L^2_loc`" in text
    assert "compactness part of `A3.2`" in text
    assert "delta_r = || W_r - W_infinity ||_Abel = O(r^(1/12))" in text
    assert "`A3.3` target and is not derived from Seregin/ESS" in text
    assert "route compatibility note" in lower
    assert "tail-flux/Abel route and the Sprint164 microlocal route separate" in text


def test_live_paper3_records_balaban_lemma3_and_defers_option_b() -> None:
    text = read_live_paper("paper3")
    squashed = squash(text)

    assert "`Balaban1988`, Lemma 3" in text
    assert "equations (2.11)-(2.13)" in text
    assert "recorded there as (2.38)" in text
    assert "|H(Z)| <= C exp(-c d(Z))" in text
    assert "polymer sums for boundary-touching and large-diameter" in text
    assert "trace-norm transfer conclusion of Theorem 5.2" in text
    assert "authority-backed theorem import, not a repo-native proof" in text
    assert "companion Option-B" in text
    assert "Kotecky-Preiss activity bound" in text
    assert "Until that separate proof exists, Theorem 5.2 remains authority-backed" in squashed


def test_live_core_papers_keep_terminal_promotion_boundaries_false() -> None:
    paper1 = read_live_paper("paper1")
    paper3 = read_live_paper("paper3")
    paper8 = read_live_paper("paper8")
    paper3_squashed = squash(paper3).lower()

    assert "terminal false guard surfaces" in paper1
    assert "no clay approval, external acceptance, or terminal promotion is asserted." in paper3_squashed
    assert "terminal-guard surfaces" in paper3
    assert "the terminal unification guard remains false." in paper8
    assert "It does not prove terminal unification." in paper8


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


def test_publication_readiness_tracks_missing_math_master_frontier() -> None:
    readiness = load_script("check_publication_readiness")
    payload, load_results = readiness.load_manifest(REPO_ROOT)
    assert [result for result in load_results if not result.ok] == []

    results = readiness.check_missing_math_master_frontier(payload, REPO_ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []

    selected = readiness.missing_math_master_frontier_rows(payload["rows"])
    assert {
        "ns-a1-a3-abel-stationarity-frontier",
        "ns-a4-defect-wall-frontier",
        "ym-h3a-balaban-frontier",
        "uct-cross-term-nullity-frontier",
    } <= set(selected)
    assert all(selected.values())
    allowed = readiness.MISSING_MATH_MASTER_FRONTIER_ALLOWED_STATUSES
    assert all(row["expected_status"] in allowed for rows in selected.values() for row in rows)


def theorem_packet_manifest_payload(readiness: ModuleType) -> dict[str, object]:
    rows = [
        {
            "paper": paper,
            "lemma": lemma,
            "exact_var": exact_var,
            "expected_status": status,
            "governance_note": "fail-closed guard blocks promotion; false/open/locked boundary",
        }
        for paper, lemma, exact_var, status in readiness.THEOREM_PACKET_MANIFEST_EXPECTATIONS
    ]
    return {"rows": rows}


def test_theorem_packet_manifest_exact_rows_are_checked() -> None:
    readiness = load_script("check_publication_readiness")

    results = readiness.check_theorem_packet_manifest_rows(theorem_packet_manifest_payload(readiness))
    assert [result for result in results if not result.ok] == []


def test_theorem_packet_manifest_check_catches_missing_and_promoting_rows() -> None:
    readiness = load_script("check_publication_readiness")
    payload = theorem_packet_manifest_payload(readiness)
    rows = payload["rows"]
    assert isinstance(rows, list)
    rows.pop()
    rows[0]["expected_status"] = "proved"
    rows[0]["governance_note"] = "promoted"

    results = readiness.check_theorem_packet_manifest_rows(payload)
    failures = {result.name: result.detail for result in results if not result.ok}

    assert "Missing-math master: UCT.8 Jordan-von Neumann" in failures[
        "theorem-packet-manifest-exact-rows"
    ]
    assert "proved" in failures["theorem-packet-manifest-nonpromoting-statuses"]


def theorem_agenda_script_text(
    *,
    id_key: str,
    ids: list[str],
    extra_markers: list[str],
    promote: bool = False,
) -> str:
    rows = [{id_key: item, "status": "open", "promotion_allowed": False} for item in ids]
    if promote:
        rows[0]["promotion_allowed"] = True
    marker_comment = " ".join([*ids, *extra_markers])
    return textwrap.dedent(
        f"""\
        #!/usr/bin/env python3
        # {marker_comment}
        import json
        print(json.dumps({{"rows": {rows!r}}}))
        """
    )


def write_theorem_agenda_fixture(
    repo_root: Path,
    readiness: ModuleType,
    *,
    omit_master_id: str | None = None,
    promote_ns_agenda: bool = False,
) -> None:
    for script in readiness.THEOREM_AGENDA_SCRIPTS:
        path = repo_root / script["path"]
        path.parent.mkdir(parents=True, exist_ok=True)
        required_ids = [str(item) for item in script["required_ids"]]
        if script["name"] == "missing-math-master-agenda" and omit_master_id is not None:
            required_ids = [item for item in required_ids if item != omit_master_id]
        path.write_text(
            theorem_agenda_script_text(
                id_key=str(script["id_key"]),
                ids=required_ids,
                extra_markers=[str(item) for item in script["source_markers"]],
                promote=promote_ns_agenda and script["name"] == "ns-abel-defect-measure-agenda",
            ),
            encoding="utf-8",
        )

    for receipt in readiness.THEOREM_AGENDA_RECEIPTS:
        receipt_path = repo_root / receipt["path"]
        receipt_path.parent.mkdir(parents=True, exist_ok=True)
        anchors = "\n".join(
            str(item)
            for item in (
                *receipt["required_anchors"],
                *receipt["required_gate_tokens"],
            )
        )
        true_fields = "\n".join(
            f"  {field} =\n    true" for field in receipt["required_true_fields"]
        )
        false_fields = "\n".join(
            f"  {field} =\n    false" for field in receipt["required_false_fields"]
        )
        receipt_path.write_text(f"{anchors}\n{true_fields}\n{false_fields}\n", encoding="utf-8")


def test_publication_readiness_checks_exact_theorem_agenda_surfaces() -> None:
    readiness = load_script("check_publication_readiness")
    results = readiness.check_theorem_agenda_surfaces(REPO_ROOT)
    failures = [result for result in results if not result.ok]
    assert failures == []

    script_names = {str(script["name"]) for script in readiness.THEOREM_AGENDA_SCRIPTS}
    assert {
        "missing-math-master-agenda",
        "ns-abel-defect-measure-agenda",
        "ym-option-b-gap-audit",
        "ns-missing-math-theorem-agenda",
        "ym-missing-math-theorem-agenda",
        "uct-missing-math-theorem-agenda",
        "full-missing-math-theorem-agenda",
    } == script_names
    receipt_paths = {receipt["path"].as_posix() for receipt in readiness.THEOREM_AGENDA_RECEIPTS}
    assert receipt_paths == {
        "DASHI/Physics/Closure/MissingMathMasterFrontierReceipt.agda",
        "DASHI/Physics/Closure/FullMissingMathTheoremAgendaBoundary.agda",
    }


def test_theorem_agenda_readiness_fails_closed_for_missing_required_packet_id(tmp_path: Path) -> None:
    readiness = load_script("check_publication_readiness")
    write_theorem_agenda_fixture(tmp_path, readiness, omit_master_id="UCT-10")

    results = readiness.check_theorem_agenda_surfaces(tmp_path)
    failures = {result.name: result.detail for result in results if not result.ok}

    assert "UCT-10" in failures["theorem-agenda-source-contract:missing-math-master-agenda"]
    assert "UCT-10" in failures["theorem-agenda-output-contract:missing-math-master-agenda"]


def test_theorem_agenda_readiness_rejects_promoting_output(tmp_path: Path) -> None:
    readiness = load_script("check_publication_readiness")
    write_theorem_agenda_fixture(tmp_path, readiness, promote_ns_agenda=True)

    results = readiness.check_theorem_agenda_surfaces(tmp_path)
    failures = {result.name: result.detail for result in results if not result.ok}

    assert "promotion_allowed=true" in failures[
        "theorem-agenda-output-contract:ns-abel-defect-measure-agenda"
    ]


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
