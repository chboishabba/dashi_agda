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
