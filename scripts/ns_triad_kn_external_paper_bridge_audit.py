#!/usr/bin/env python3
"""Audit the ACL and Shahmurov external-paper bridge for the mixed-tail lane.

This is a candidate-only, fail-closed report generator. It does not prove any
Navier-Stokes theorem. It checks that the local PDFs contain the expected
carrier statements and emits a small summary for the current bridge note.
"""

from __future__ import annotations

import json
import shutil
import subprocess
from dataclasses import dataclass, asdict
from pathlib import Path
from typing import Iterable


REPO_ROOT = Path(__file__).resolve().parents[1]
OUT_DIR = (
    REPO_ROOT
    / "scripts"
    / "data"
    / "outputs"
    / "ns_boundary_pressure_geometric_20260621"
    / "ns_triad_kn_external_paper_bridge_audit_20260624"
)

FIELDS_PDF = Path("/home/c/Downloads/D663F306-4179-11F1-A876-C7C17E70DEF5.pdf")
SHAHMUROV_PDF = Path("/home/c/Downloads/2606.07875v1.pdf")


@dataclass(frozen=True)
class PaperAudit:
    name: str
    pdf_path: str
    page_count: int | None
    keywords_found: dict[str, bool]
    snippets: dict[str, str]
    candidate_only: bool
    theorem_promotion: bool
    full_ns_promotion: bool
    clay_promotion: bool


def pdf_text(path: Path) -> str:
    if not path.exists():
        raise FileNotFoundError(path)
    if shutil.which("pdftotext") is None:
        raise RuntimeError("pdftotext is required for this audit script")
    return subprocess.check_output(["pdftotext", str(path), "-"], text=True, stderr=subprocess.STDOUT)


def page_count(path: Path) -> int | None:
    try:
        out = subprocess.check_output(["pdfinfo", str(path)], text=True, stderr=subprocess.STDOUT)
    except Exception:
        return None
    for line in out.splitlines():
        if line.startswith("Pages:"):
            try:
                return int(line.split(":", 1)[1].strip())
            except ValueError:
                return None
    return None


def snippet(text: str, needle: str, width: int = 220) -> str:
    low = text.lower()
    idx = low.find(needle.lower())
    if idx < 0:
        return ""
    start = max(0, idx - width)
    end = min(len(text), idx + len(needle) + width)
    return " ".join(text[start:end].split())


def found(text: str, needles: Iterable[str]) -> dict[str, bool]:
    low = text.lower()
    return {needle: needle.lower() in low for needle in needles}


def audit_fields() -> PaperAudit:
    text = pdf_text(FIELDS_PDF)
    needles = [
        "Angular Cancellation Lemma",
        "Theorem 4.27",
        "unit-width shells",
        "G(k,p)",
        "resonant set",
    ]
    return PaperAudit(
        name="Fields ACL",
        pdf_path=str(FIELDS_PDF),
        page_count=page_count(FIELDS_PDF),
        keywords_found=found(text, needles),
        snippets={needle: snippet(text, needle) for needle in needles},
        candidate_only=True,
        theorem_promotion=False,
        full_ns_promotion=False,
        clay_promotion=False,
    )


def audit_shahmurov() -> PaperAudit:
    text = pdf_text(SHAHMUROV_PDF)
    needles = [
        "Theorem 2.2",
        "Corollary 2.3",
        "axisymmetric-with-swirl",
        "reduction theorem",
        "companion axisymmetric-with-swirl endpoint theorem",
    ]
    return PaperAudit(
        name="Shahmurov reduction",
        pdf_path=str(SHAHMUROV_PDF),
        page_count=page_count(SHAHMUROV_PDF),
        keywords_found=found(text, needles),
        snippets={needle: snippet(text, needle) for needle in needles},
        candidate_only=True,
        theorem_promotion=False,
        full_ns_promotion=False,
        clay_promotion=False,
    )


def write_markdown(out_path: Path, payload: dict) -> None:
    lines = []
    lines.append("# NS triad K_N external paper bridge audit")
    lines.append("")
    lines.append("Candidate-only, fail-closed audit of the Fields ACL paper and the Shahmurov reduction paper.")
    lines.append("")
    for audit in payload["papers"]:
        lines.append(f"## {audit['name']}")
        lines.append("")
        lines.append(f"- pdf: `{audit['pdf_path']}`")
        lines.append(f"- pages: `{audit['page_count']}`")
        lines.append(f"- candidate-only: `{str(audit['candidate_only']).lower()}`")
        lines.append(f"- theorem promotion: `{str(audit['theorem_promotion']).lower()}`")
        lines.append(f"- full-NS promotion: `{str(audit['full_ns_promotion']).lower()}`")
        lines.append(f"- Clay promotion: `{str(audit['clay_promotion']).lower()}`")
        lines.append("")
        lines.append("Keywords checked:")
        for key, ok in audit["keywords_found"].items():
            lines.append(f"- `{key}`: `{str(ok).lower()}`")
        lines.append("")
        lines.append("Snippets:")
        for key, snip in audit["snippets"].items():
            lines.append(f"- `{key}`: {snip if snip else '[not found]'}")
        lines.append("")
    lines.append("## Bridge conclusion")
    lines.append("")
    lines.append("- Fields ACL is a candidate carrier for the SchurResidueScale off-diagonal block question.")
    lines.append("- Shahmurov is a candidate carrier for the endpoint-reduction / residence bridge, conditional on the missing AS theorem.")
    lines.append("- Neither paper upgrades theorem, full-NS, or Clay authority.")
    out_path.write_text("\n".join(lines) + "\n", encoding="utf-8")


def main() -> None:
    fields = audit_fields()
    shahmurov = audit_shahmurov()

    OUT_DIR.mkdir(parents=True, exist_ok=True)
    payload = {
        "status": "ok",
        "candidate_only": True,
        "theorem_promotion": False,
        "full_ns_promotion": False,
        "clay_promotion": False,
        "papers": [asdict(fields), asdict(shahmurov)],
        "bridge_readout": [
            "Fields ACL -> SchurResidueScale carrier candidate only",
            "Shahmurov reduction -> endpoint-reduction carrier candidate only",
        ],
    }

    json_path = OUT_DIR / "summary.json"
    md_path = OUT_DIR / "summary.md"
    json_path.write_text(json.dumps(payload, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    write_markdown(md_path, payload)
    print(json.dumps(payload, indent=2, sort_keys=True))


if __name__ == "__main__":
    main()
