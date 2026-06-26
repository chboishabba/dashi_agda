from __future__ import annotations

import importlib.util
import sys
from pathlib import Path
from types import ModuleType


REPO_ROOT = Path(__file__).resolve().parents[1]


def load_renderer() -> ModuleType:
    path = REPO_ROOT / "scripts" / "render_core_paper_pdfs.py"
    spec = importlib.util.spec_from_file_location("render_core_paper_pdfs", path)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = module
    spec.loader.exec_module(module)
    return module


def test_render_all_skip_pdf_generates_tex_and_bib_without_latexmk(
    tmp_path: Path, monkeypatch
) -> None:
    renderer = load_renderer()

    def fail_latexmk(_tex_path: Path) -> None:
        raise AssertionError("skip_pdf=True must not invoke latexmk")

    monkeypatch.setattr(renderer, "run_latexmk", fail_latexmk)

    renderer.render_all(tmp_path, skip_pdf=True)

    expected_tex = {
        "paper1_navier_stokes.tex",
        "paper3_yang_mills.tex",
        "paper8_closure_architecture.tex",
    }
    assert expected_tex <= {path.name for path in tmp_path.glob("*.tex")}
    assert (tmp_path / "core_references.bib").exists()


def test_generated_tex_uses_final_author_and_no_author_placeholders(tmp_path: Path) -> None:
    renderer = load_renderer()
    renderer.render_all(tmp_path, skip_pdf=True)

    combined_tex = "\n".join(path.read_text(encoding="utf-8") for path in tmp_path.glob("*.tex"))
    assert combined_tex.count(r"\author{Johl Brown}") == 3
    assert r"\author{DASHI project}" not in combined_tex
    assert "Pending final public author list" not in combined_tex
    assert "pending final public author" not in combined_tex.lower()


def test_generated_bib_resolves_reader_facing_references_without_ledger_placeholder(
    tmp_path: Path,
) -> None:
    renderer = load_renderer()
    renderer.render_all(tmp_path, skip_pdf=True)

    bib = (tmp_path / "core_references.bib").read_text(encoding="utf-8")
    assert "See common citation ledger" not in bib
    assert "see common citation ledger" not in bib.lower()
    assert "@article{LerayHopf" in bib
    assert "@article{CKN" in bib
    assert "@article{Balaban1988" in bib or "@misc{Balaban1988" in bib


def test_referenced_seregin_ess_and_balaban_keys_are_emitted(tmp_path: Path) -> None:
    renderer = load_renderer()
    renderer.render_all(tmp_path, skip_pdf=True)

    generated_tex = {
        path.name: path.read_text(encoding="utf-8") for path in tmp_path.glob("*.tex")
    }
    bib = (tmp_path / "core_references.bib").read_text(encoding="utf-8")

    paper1_tex = generated_tex["paper1_navier_stokes.tex"]
    assert "Seregin2012" in paper1_tex
    assert "ESS2003" in paper1_tex
    assert "@misc{Seregin2012" in bib or "@article{Seregin2012" in bib
    assert "@misc{ESS2003" in bib or "@article{ESS2003" in bib

    paper3_tex = generated_tex["paper3_yang_mills.tex"]
    assert "Balaban1988" in paper3_tex
    assert "Balaban1987" in paper3_tex
    assert "@misc{Balaban1987" in bib or "@article{Balaban1987" in bib
    assert "@misc{Balaban1988" in bib or "@article{Balaban1988" in bib
