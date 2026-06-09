#!/usr/bin/env python3
"""Build Sprint 104 Clay candidate dossier artifacts from repo evidence."""

from __future__ import annotations

import argparse
import json
import re
import subprocess
from dataclasses import dataclass
from pathlib import Path
from typing import Any


DEFAULT_OUT_DIR = Path("outputs/ym_sprint104_clay_dossier_builder")
SUMMARY_NAME = "ym_sprint104_clay_dossier_builder_summary.json"
MODULE_GLOB = "DASHI/Physics/Closure/YMSprint*.agda"
SUMMARY_GLOB = "outputs/ym_sprint*/ym_sprint*_summary.json"


@dataclass(frozen=True)
class BlockedRequirement:
    gap_id: str
    clay_requirement: str
    evidence: str
    reason: str
    required_resolution: str


@dataclass(frozen=True)
class RedTeamItem:
    objection_id: str
    objection: str
    evidence_source: str
    current_status: str
    required_resolution: str


BLOCKED_REQUIREMENTS: tuple[BlockedRequirement, ...] = (
    BlockedRequirement(
        "blockedWightmanDistributions",
        "Construct Wightman distributions for the four-dimensional theory.",
        "OS/Wightman authority and boundary receipts are present, but no complete distribution-level reconstruction proof is present in Sprint 91-103.",
        "Partial OS material is not a completed Wightman reconstruction.",
        "Complete OS-to-Wightman reconstruction for the candidate Schwinger functions.",
    ),
    BlockedRequirement(
        "blockedPoincareCovariance",
        "Prove Poincare covariance of the reconstructed Wightman theory.",
        "Euclidean and transfer-boundary receipts exist, but the Minkowski covariance theorem is not closed.",
        "Euclidean-invariance evidence alone does not establish Lorentzian covariance.",
        "Derive Poincare covariance after reconstruction and bind it to the candidate field algebra.",
    ),
    BlockedRequirement(
        "blockedSpectrumCondition",
        "Prove the positive-energy spectrum condition.",
        "Transfer-gap and OS boundary material exists, but the Wightman spectrum theorem is not closed.",
        "A transfer-gap receipt is not itself the spectrum condition.",
        "Prove the energy-momentum spectrum lies in the closed forward cone and bind the gap to that spectrum.",
    ),
    BlockedRequirement(
        "blockedAllCompactSimpleG",
        "Prove the theorem for any compact simple gauge group G.",
        "The current manuscript lane is SU(3)-scoped.",
        "The Jaffe-Witten problem is not restricted to SU(3).",
        "Generalize group-dependent estimates and nontriviality witnesses to arbitrary compact simple G.",
    ),
    BlockedRequirement(
        "blockedNonCircularMassGapProof",
        "Prove the mass gap without assuming the physical mass scale.",
        "Sprint 103 records a continuum bridge using WC3, RG effective mass, transfer comparison, and asymptotic freedom.",
        "Sprint 104 cannot certify that the route avoids circular dependence on the desired gap.",
        "Prove WC3-controlled small-field expansion gives m_eff(a) > 0, then use asymptotic freedom for physical scale behavior.",
    ),
)


RED_TEAM_ITEMS: tuple[RedTeamItem, ...] = (
    RedTeamItem(
        "circularity-risk",
        "The continuum mass-gap lane may assume the physical mass scale it aims to prove.",
        "DASHI/Physics/Closure/YMSprint103ContinuumMassGapObligation7.agda",
        "blocked",
        "Separate m_eff(a) > 0 from WC3 small-field control before invoking asymptotic freedom.",
    ),
    RedTeamItem(
        "wightman-gap",
        "Partial OS material is not a completed Wightman theory.",
        "DASHI/Physics/Closure/YMOSWightmanReconstructionAuthority.agda and Sprint 104 blocked-gap records",
        "blocked",
        "Complete reconstruction, covariance, locality, temperedness, positivity, and spectrum condition.",
    ),
    RedTeamItem(
        "group-scope-gap",
        "The current candidate lane is SU(3)-scoped while Clay asks for any compact simple G.",
        "DASHI/Physics/Closure/YMSprint103NontrivialSU3ContinuumMeasureObligation8.agda",
        "blocked",
        "Generalize every group-dependent estimate and witness beyond SU(3).",
    ),
    RedTeamItem(
        "external-acceptance-boundary",
        "The repo cannot self-issue Clay acceptance.",
        "https://www.claymath.org/millennium-problems/rules/",
        "external-boundary",
        "Qualifying publication, elapsed time, and broad mathematical acceptance are external gates.",
    ),
)


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path("."))
    parser.add_argument("--out-dir", type=Path, default=DEFAULT_OUT_DIR)
    return parser.parse_args()


def sprint_number(path: Path) -> int | None:
    match = re.search(r"YMSprint(\d+)", path.name)
    if match is None:
        return None
    return int(match.group(1))


def read_sprint_modules(repo_root: Path) -> dict[str, str]:
    modules: dict[str, str] = {}
    for path in sorted(repo_root.glob(MODULE_GLOB)):
        number = sprint_number(path)
        if number is not None and 91 <= number <= 103:
            modules[str(path.relative_to(repo_root))] = path.read_text()
    return modules


def read_summary_files(repo_root: Path) -> dict[str, Any]:
    summaries: dict[str, Any] = {}
    for path in sorted(repo_root.glob(SUMMARY_GLOB)):
        match = re.search(r"ym_sprint(\d+)", str(path))
        if match is None:
            continue
        number = int(match.group(1))
        if 91 <= number <= 103:
            summaries[str(path.relative_to(repo_root))] = json.loads(path.read_text())
    return summaries


def parse_imports(text: str) -> list[str]:
    imports: list[str] = []
    for match in re.finditer(r"(?m)^\s*import\s+([A-Za-z0-9_.]+)", text):
        imports.append(match.group(1))
    return sorted(dict.fromkeys(imports))


def git_tag_exists(repo_root: Path, tag_name: str) -> bool:
    result = subprocess.run(
        ["git", "tag", "--list", tag_name],
        cwd=repo_root,
        check=True,
        text=True,
        stdout=subprocess.PIPE,
    )
    return result.stdout.strip() == tag_name


def clay_promotion_hits(modules: dict[str, str]) -> list[str]:
    return sorted(
        path
        for path, text in modules.items()
        if re.search(r"(?m)^\s*clayYangMillsPromoted\s*=\s*true\s*$", text)
    )


def dependency_graph(modules: dict[str, str], summaries: dict[str, Any]) -> dict[str, Any]:
    nodes: list[dict[str, Any]] = []
    edges: list[dict[str, str]] = []
    module_names = {
        path: path.removesuffix(".agda").replace("/", ".") for path in modules
    }
    module_name_to_path = {name: path for path, name in module_names.items()}

    for path, text in modules.items():
        imports = parse_imports(text)
        nodes.append(
            {
                "id": path,
                "kind": "agda-module",
                "sprint": sprint_number(Path(path)),
                "imports": imports,
                "evidence": "actual repo file",
            }
        )
        for imported in imports:
            imported_path = module_name_to_path.get(imported)
            if imported_path is not None:
                edges.append(
                    {
                        "from": path,
                        "to": imported_path,
                        "kind": "agda-import",
                    }
                )

    for path, data in summaries.items():
        nodes.append(
            {
                "id": path,
                "kind": "audit-summary",
                "sprint": data.get("sprint"),
                "route_decision": data.get("route_decision"),
                "evidence": "actual generated summary file",
            }
        )

    return {"nodes": nodes, "edges": edges}


def evidence_sections(
    modules: dict[str, str],
    summaries: dict[str, Any],
) -> list[dict[str, Any]]:
    required = [
        (
            "wc3-control",
            "WC3 and Dobrushin Control",
            ["GaugeCovariantDobrushinComparison", "WC3UniformClusterSummability"],
        ),
        (
            "continuum-mass-gap-route",
            "Continuum Mass Gap Candidate Route",
            ["ContinuumLimitMassGap", "RGInvariantPhysicalScale"],
        ),
        (
            "su3-nontriviality",
            "SU(3) Nontriviality Candidate",
            ["Nontrivial4DSU3YangMillsMeasure", "SU(3)"],
        ),
        (
            "external-boundary",
            "Clay External Boundary",
            ["externalAcceptanceTokenAvailable", "clayYangMillsPromoted"],
        ),
    ]
    sections: list[dict[str, Any]] = []
    for section_id, title, anchors in required:
        evidence: list[dict[str, str]] = []
        for path, text in modules.items():
            hits = [anchor for anchor in anchors if anchor in text]
            if hits:
                evidence.append(
                    {
                        "source": path,
                        "anchors": ", ".join(hits),
                    }
                )
        for path, data in summaries.items():
            encoded = json.dumps(data, sort_keys=True)
            hits = [anchor for anchor in anchors if anchor in encoded]
            if hits:
                evidence.append(
                    {
                        "source": path,
                        "anchors": ", ".join(hits),
                    }
                )
        sections.append(
            {
                "section_id": section_id,
                "title": title,
                "evidence": evidence,
                "status": "evidence-backed" if evidence else "blocked-no-evidence",
            }
        )
    return sections


def build_summary(repo_root: Path) -> dict[str, Any]:
    modules = read_sprint_modules(repo_root)
    summaries = read_summary_files(repo_root)
    graph = dependency_graph(modules, summaries)
    sections = evidence_sections(modules, summaries)
    promotion_hits = clay_promotion_hits(modules)
    freeze_tag = git_tag_exists(repo_root, "sprint-103-receipt-freeze")
    graph_ok = len(modules) >= 13 and len(summaries) >= 10
    sections_ok = all(section["evidence"] for section in sections)

    return {
        "sprint": "104-clay-candidate-dossier-builder",
        "repo_root": str(repo_root.resolve()),
        "freeze": {
            "tag": "sprint-103-receipt-freeze",
            "present": freeze_tag,
        },
        "dependency_graph": graph,
        "module_count": len(modules),
        "summary_count": len(summaries),
        "dossier_sections": sections,
        "blocked_clay_requirements": [
            requirement.__dict__ for requirement in BLOCKED_REQUIREMENTS
        ],
        "red_team_checklist": [item.__dict__ for item in RED_TEAM_ITEMS],
        "external_boundaries": [
            {
                "boundary_id": "clay-unsolved-status",
                "source": "https://www.claymath.org/millennium/yang-mills-the-maths-gap/",
                "status": "CMI lists Yang-Mills and the mass gap as unsolved.",
            },
            {
                "boundary_id": "clay-rules",
                "source": "https://www.claymath.org/millennium-problems/rules/",
                "status": "CMI rules require qualifying publication, elapsed time, and broad acceptance.",
            },
        ],
        "clay_promotion": {
            "clayYangMillsPromoted": bool(promotion_hits),
            "true_promotion_modules": promotion_hits,
            "no_clay_promotion": not promotion_hits,
        },
        "route_decision": (
            "SPRINT104_COMPLETE_DOSSIER_BUILDER_WITH_BLOCKED_CLAY_GAPS"
            if freeze_tag and graph_ok and sections_ok and not promotion_hits
            else "SPRINT104_FAIL_CLOSED"
        ),
    }


def write_json(path: Path, data: Any) -> None:
    path.write_text(json.dumps(data, indent=2, sort_keys=True) + "\n")


def write_dependency_markdown(path: Path, graph: dict[str, Any]) -> None:
    lines = [
        "# Sprint 104 Dependency Graph",
        "",
        "Generated from Sprint 91-103 Agda modules and audit summary files.",
        "",
        "## Nodes",
        "",
    ]
    for node in graph["nodes"]:
        lines.append(f"- `{node['id']}` ({node['kind']})")
    lines.extend(["", "## Edges", ""])
    for edge in graph["edges"]:
        lines.append(f"- `{edge['from']}` imports `{edge['to']}`")
    path.write_text("\n".join(lines) + "\n")


def write_dossier_markdown(path: Path, summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 104 Clay Candidate Dossier",
        "",
        "This dossier records only evidence found in the repository. Open Clay requirements are listed as blocked requirements.",
        "",
        "## Candidate Lane",
        "",
        "Current lane: SU(3) candidate manuscript evidence, not a Clay promotion.",
        "",
        "## Evidence-Backed Sections",
        "",
    ]
    for section in summary["dossier_sections"]:
        lines.append(f"### {section['title']}")
        for item in section["evidence"]:
            lines.append(f"- `{item['source']}`: {item['anchors']}")
        lines.append("")
    lines.extend(
        [
            "## Required Non-Circular Route",
            "",
            "WC3-controlled small-field expansion must prove `m_eff(a) > 0`; asymptotic freedom may then supply physical scale behavior. This is blocked until the non-circular route is proved.",
            "",
            "## Blocked Clay Requirements",
            "",
        ]
    )
    for requirement in summary["blocked_clay_requirements"]:
        lines.append(f"### {requirement['gap_id']}")
        lines.append(f"- Requirement: {requirement['clay_requirement']}")
        lines.append(f"- Evidence: {requirement['evidence']}")
        lines.append(f"- Reason: {requirement['reason']}")
        lines.append(f"- Required resolution: {requirement['required_resolution']}")
        lines.append("")
    lines.extend(
        [
            "## External Boundaries",
            "",
        ]
    )
    for boundary in summary["external_boundaries"]:
        lines.append(f"- `{boundary['boundary_id']}`: {boundary['source']} - {boundary['status']}")
    path.write_text("\n".join(lines) + "\n")


def write_red_team_markdown(path: Path, summary: dict[str, Any]) -> None:
    lines = [
        "# Sprint 104 Red-Team Checklist",
        "",
        "Each item has a concrete objection, evidence source, status, and required resolution.",
        "",
    ]
    for item in summary["red_team_checklist"]:
        lines.append(f"## {item['objection_id']}")
        lines.append(f"- Objection: {item['objection']}")
        lines.append(f"- Evidence source: {item['evidence_source']}")
        lines.append(f"- Current status: {item['current_status']}")
        lines.append(f"- Required resolution: {item['required_resolution']}")
        lines.append("")
    path.write_text("\n".join(lines) + "\n")


def write_outputs(summary: dict[str, Any], out_dir: Path) -> None:
    out_dir.mkdir(parents=True, exist_ok=True)
    write_json(out_dir / SUMMARY_NAME, summary)
    write_json(out_dir / "dependency_graph.json", summary["dependency_graph"])
    write_dependency_markdown(out_dir / "dependency_graph.md", summary["dependency_graph"])
    write_dossier_markdown(out_dir / "clay_candidate_dossier.md", summary)
    write_red_team_markdown(out_dir / "red_team_checklist.md", summary)


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    out_dir = args.out_dir
    if not out_dir.is_absolute():
        out_dir = repo_root / out_dir
    summary = build_summary(repo_root)
    write_outputs(summary, out_dir)
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
