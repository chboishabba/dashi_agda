#!/usr/bin/env python3
"""Audit agenda for the first NS Abel defect-measure frontier.

This CLI inspects the repository for the A1.1-A1.3 and A3.1-A3.4 marker
surface around AbelTriadicDefectMeasureConstruction and approximate
stationarity.  It reports concrete gate rows and finite normal-form constants,
but it is deliberately fail-closed: it does not construct a PDE measure, prove
stationarity, or promote a Clay claim.
"""

from __future__ import annotations

import argparse
import json
import math
import re
from dataclasses import asdict, dataclass
from fractions import Fraction
from pathlib import Path
from typing import Sequence


TEXT_SUFFIXES = {
    ".agda",
    ".cfg",
    ".csv",
    ".json",
    ".md",
    ".py",
    ".rst",
    ".toml",
    ".tsv",
    ".txt",
    ".yaml",
    ".yml",
}

SKIP_DIRS = {
    ".git",
    ".mypy_cache",
    ".pytest_cache",
    ".venv",
    "__pycache__",
    "artifacts",
    "build",
    "dist",
    "generated",
    "Images",
    "monster",
    "node_modules",
    "outputs",
    "temp-DOWNLOADED",
}


@dataclass(frozen=True)
class EvidenceHit:
    path: str
    matched_terms: list[str]
    occurrence_count: int


@dataclass(frozen=True)
class GateRow:
    marker: str
    gate: str
    obligation: str
    required_for: str
    marker_terms: list[str]
    evidence_files: list[EvidenceHit]
    evidence_file_count: int
    occurrence_count: int
    marker_present: bool
    diagnostic_status: str
    proof_status: str


@dataclass(frozen=True)
class DeltaRateCheck:
    raw: str
    numerator: int
    denominator: int
    value: float
    positive: bool
    below_one: bool
    admissible_proxy_exponent: bool


def parse_args(argv: Sequence[str] | None = None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--repo-root",
        type=Path,
        default=Path(__file__).resolve().parents[1],
        help="Repository root to inspect.",
    )
    parser.add_argument(
        "--format",
        choices=("json", "md"),
        default="json",
        help="Output format. JSON is the default.",
    )
    parser.add_argument(
        "--delta-rate-exponent",
        default="1/12",
        help="Candidate exponent alpha in delta_r = O(r^alpha).",
    )
    parser.add_argument(
        "--max-evidence-files",
        type=int,
        default=6,
        help="Maximum evidence files retained per gate row.",
    )
    return parser.parse_args(argv)


def gate_specs() -> list[dict[str, object]]:
    return [
        {
            "marker": "A1.1",
            "gate": "bounded Abel mass",
            "obligation": "Uniform Abel-weighted triadic defect mass bound.",
            "required_for": "finite Radon measure branch and A1/A3 bootstrap input",
            "terms": [
                "A1.1",
                "BoundedAbelMass",
                "bounded Abel mass",
                "bounded Abel-weighted defect mass",
                "recordA11BoundedAbelWeightedDefectMassContract",
            ],
        },
        {
            "marker": "A1.2",
            "gate": "weak-* compactness",
            "obligation": "Tightness/precompactness of the bounded Abel branch.",
            "required_for": "weak-* extraction of an Abel triadic defect measure",
            "terms": [
                "A1.2",
                "WeakStar",
                "weak-*",
                "weak star",
                "precompactness",
                "tightness",
                "recordA12WeakStarTightnessContract",
            ],
        },
        {
            "marker": "A1.3",
            "gate": "shell-tail control",
            "obligation": "Quantitative reciprocal-shell tail control uniform in r.",
            "required_for": "tightness and closure of Abel-window estimates",
            "terms": [
                "A1.3",
                "ShellTail",
                "shell-tail",
                "shell tail",
                "Tail_A1",
                "recordA13QuantitativeShellTailContract",
            ],
        },
        {
            "marker": "A3.1",
            "gate": "energy ODE for W_r",
            "obligation": "Localized Abel-window energy ODE for W_r = U_r - U_infinity.",
            "required_for": "stationarity-rate control fed by A1 mass",
            "terms": [
                "A3.1",
                "energy ODE",
                "EnergyODE",
                "W_r",
                "U_r - U_infinity",
                "U_r - U_infty",
            ],
        },
        {
            "marker": "A3.2",
            "gate": "Seregin/ESS intake",
            "obligation": "Import Seregin/ESS compactness and epsilon-rate input without deriving the Abel rate from it.",
            "required_for": "external compactness/rate source used by A3",
            "terms": [
                "A3.2",
                "Seregin",
                "ESS",
                "Escauriaza",
                "epsilon-rate",
                "Seregin/ESS",
            ],
        },
        {
            "marker": "A3.3",
            "gate": "delta_r -> 0 stationarity",
            "obligation": "Quantitative approximate T_NS stationarity with delta_r tending to zero.",
            "required_for": "bias-neutrality and downstream stationary defect consumers",
            "terms": [
                "A3.3",
                "delta_r -> 0",
                "delta_r = O",
                "stationarity-defect",
                "stationarity defect",
                "approximate T_NS",
                "ApproximateTNSStationarity",
            ],
        },
        {
            "marker": "A3.4",
            "gate": "Abel summation closure",
            "obligation": "Multiscale Abel summation with no hidden exponent loss.",
            "required_for": "closing the A1/A3 bootstrap before A4 handoff",
            "terms": [
                "A3.4",
                "Abel-summation",
                "Abel summation",
                "multiscale Abel",
                "summation closure",
                "MultiscaleAbelSummation",
            ],
        },
    ]


def iter_text_files(repo_root: Path) -> list[Path]:
    files: list[Path] = []
    self_path = Path(__file__).resolve()
    for path in repo_root.rglob("*"):
        if any(part in SKIP_DIRS for part in path.relative_to(repo_root).parts):
            continue
        if path.name.startswith("all_code") and path.suffix == ".txt":
            continue
        if path.resolve() == self_path:
            continue
        if path.is_file() and path.suffix.lower() in TEXT_SUFFIXES:
            files.append(path)
    return sorted(files)


def read_text(path: Path) -> str:
    try:
        return path.read_text(encoding="utf-8")
    except UnicodeDecodeError:
        return path.read_text(encoding="utf-8", errors="ignore")


def count_term(text_lower: str, term: str) -> int:
    term_lower = term.lower()
    if re.fullmatch(r"[a-z0-9_]+", term_lower):
        pattern = r"(?<![a-z0-9_])" + re.escape(term_lower) + r"(?![a-z0-9_])"
        return len(re.findall(pattern, text_lower))
    return text_lower.count(term_lower)


def evidence_for_terms(
    *,
    files: Sequence[Path],
    repo_root: Path,
    primary_marker: str,
    terms: Sequence[str],
    max_evidence_files: int,
) -> tuple[list[EvidenceHit], int, int]:
    all_hits: list[EvidenceHit] = []
    total_occurrences = 0
    for path in files:
        text = read_text(path)
        text_lower = text.lower()
        matched_terms: list[str] = []
        occurrence_count = 0
        for term in terms:
            count = count_term(text_lower, term)
            if count > 0:
                matched_terms.append(term)
                occurrence_count += count
        if occurrence_count > 0:
            total_occurrences += occurrence_count
            all_hits.append(
                EvidenceHit(
                    path=str(path.relative_to(repo_root)),
                    matched_terms=matched_terms,
                    occurrence_count=occurrence_count,
                )
            )
    marker_lower = primary_marker.lower()

    def evidence_rank(hit: EvidenceHit) -> tuple[int, int, int, str]:
        path_lower = hit.path.lower()
        marker_hit = any(term.lower() == marker_lower for term in hit.matched_terms)
        ns_frontier = (
            "/ns" in "/" + path_lower
            or "navierstokes" in path_lower
            or "navier-stokes" in path_lower
        )
        return (0 if marker_hit else 1, 0 if ns_frontier else 1, -hit.occurrence_count, hit.path)

    all_hits.sort(key=evidence_rank)
    return all_hits[:max_evidence_files], len(all_hits), total_occurrences


def parse_delta_rate(raw: str) -> DeltaRateCheck:
    try:
        fraction = Fraction(raw)
    except ValueError:
        value = float(raw)
        if not math.isfinite(value):
            raise ValueError("--delta-rate-exponent must be finite") from None
        fraction = Fraction(value).limit_denominator(1_000_000)
    value = float(fraction)
    positive = value > 0.0
    below_one = value < 1.0
    return DeltaRateCheck(
        raw=raw,
        numerator=fraction.numerator,
        denominator=fraction.denominator,
        value=value,
        positive=positive,
        below_one=below_one,
        admissible_proxy_exponent=positive and below_one,
    )


def build_gate_rows(
    *,
    repo_root: Path,
    max_evidence_files: int,
) -> list[GateRow]:
    files = iter_text_files(repo_root)
    rows: list[GateRow] = []
    for spec in gate_specs():
        terms = list(spec["terms"])  # type: ignore[arg-type]
        evidence, evidence_file_count, occurrence_count = evidence_for_terms(
            files=files,
            repo_root=repo_root,
            primary_marker=str(spec["marker"]),
            terms=terms,
            max_evidence_files=max_evidence_files,
        )
        present = evidence_file_count > 0
        rows.append(
            GateRow(
                marker=str(spec["marker"]),
                gate=str(spec["gate"]),
                obligation=str(spec["obligation"]),
                required_for=str(spec["required_for"]),
                marker_terms=terms,
                evidence_files=evidence,
                evidence_file_count=evidence_file_count,
                occurrence_count=occurrence_count,
                marker_present=present,
                diagnostic_status="marker_recorded" if present else "marker_missing",
                proof_status="boundary_or_agenda_only_not_proved",
            )
        )
    return rows


def build_report(args: argparse.Namespace) -> dict[str, object]:
    repo_root = args.repo_root.resolve()
    if not repo_root.exists():
        raise FileNotFoundError(f"repo root does not exist: {repo_root}")
    if args.max_evidence_files < 1:
        raise ValueError("--max-evidence-files must be positive")
    delta = parse_delta_rate(args.delta_rate_exponent)
    rows = build_gate_rows(repo_root=repo_root, max_evidence_files=args.max_evidence_files)
    checks = {
        "all_gate_markers_present": all(row.marker_present for row in rows),
        "delta_rate_exponent_positive": delta.positive,
        "delta_rate_exponent_below_one": delta.below_one,
        "promotion_flags_fail_closed": True,
    }
    return {
        "audit": "ns_abel_defect_measure_agenda",
        "frontier": "AbelTriadicDefectMeasureConstruction + approximate stationarity",
        "repo_root": str(repo_root),
        "gate_rows": [asdict(row) for row in rows],
        "finite_normal_form": {
            "kappa_distribution": "arcsine",
            "E[kappa^2]": 0.5,
            "E[kappa^4]": 0.375,
            "E[lambda^2]": 11.0 / 60.0,
            "lambda_squared_exact": "11/60",
            "kappa_bias_constant_sqrt_11_60": math.sqrt(11.0 / 60.0),
        },
        "delta_rate": asdict(delta),
        "pde_measure_constructed": False,
        "stationarity_proved": False,
        "clay_promotion": False,
        "checks": checks,
        "ok": bool(
            checks["all_gate_markers_present"]
            and checks["delta_rate_exponent_positive"]
            and checks["delta_rate_exponent_below_one"]
            and checks["promotion_flags_fail_closed"]
        ),
        "orf": {
            "O": "Worker 2 owns only scripts/ns_abel_defect_measure_agenda.py for the first NS Abel/stationarity frontier audit.",
            "R": "Inspect A1.1-A1.3 and A3.1-A3.4 markers; emit JSON by default and Markdown with --format md; keep PDE/stationarity/Clay flags false.",
            "C": "Reads repository text files and reports marker evidence for AbelTriadicDefectMeasureConstruction plus approximate stationarity gates.",
            "S": "Finite diagnostic agenda, not an Agda edit, theorem receipt, or proof promotion.",
            "L": "A1 bounded mass -> weak-* compactness -> shell-tail control -> A3 energy/Seregin intake -> delta_r -> 0 -> Abel summation closure.",
            "P": "Use gate rows to locate recorded boundary markers and expose the remaining proof obligations.",
            "G": "Fail closed unless all requested markers are visible and the supplied delta exponent is positive and below one.",
            "F": "Missing work remains PDE Abel measure construction, actual approximate stationarity proof, and downstream Clay promotion.",
        },
    }


def md_escape(value: object) -> str:
    return str(value).replace("|", "\\|").replace("\n", " ")


def render_markdown(report: dict[str, object]) -> str:
    lines: list[str] = []
    lines.append("# NS Abel Defect Measure Agenda")
    lines.append("")
    lines.append(f"- Frontier: `{report['frontier']}`")
    lines.append(f"- PDE measure constructed: `{str(report['pde_measure_constructed']).lower()}`")
    lines.append(f"- Stationarity proved: `{str(report['stationarity_proved']).lower()}`")
    lines.append(f"- Clay promotion: `{str(report['clay_promotion']).lower()}`")
    delta = report["delta_rate"]  # type: ignore[assignment]
    assert isinstance(delta, dict)
    lines.append(
        "- Delta exponent: "
        f"`{delta['raw']}` = `{delta['value']}` "
        f"(positive `{str(delta['positive']).lower()}`, below one `{str(delta['below_one']).lower()}`)"
    )
    lines.append("")
    lines.append("## Gate Rows")
    lines.append("")
    lines.append(
        "| Marker | Gate | Present | Evidence Files | Occurrences | Proof Status |"
    )
    lines.append("| --- | --- | ---: | ---: | ---: | --- |")
    for row_obj in report["gate_rows"]:  # type: ignore[index]
        row = row_obj
        assert isinstance(row, dict)
        lines.append(
            "| "
            + " | ".join(
                [
                    md_escape(row["marker"]),
                    md_escape(row["gate"]),
                    md_escape(str(row["marker_present"]).lower()),
                    md_escape(row["evidence_file_count"]),
                    md_escape(row["occurrence_count"]),
                    md_escape(row["proof_status"]),
                ]
            )
            + " |"
        )
    lines.append("")
    lines.append("## Finite Normal Form")
    lines.append("")
    normal = report["finite_normal_form"]
    assert isinstance(normal, dict)
    for key in [
        "kappa_distribution",
        "E[kappa^2]",
        "E[kappa^4]",
        "E[lambda^2]",
        "lambda_squared_exact",
    ]:
        lines.append(f"- `{key}`: `{normal[key]}`")
    return "\n".join(lines)


def main(argv: Sequence[str] | None = None) -> int:
    args = parse_args(argv)
    report = build_report(args)
    if args.format == "md":
        print(render_markdown(report))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
