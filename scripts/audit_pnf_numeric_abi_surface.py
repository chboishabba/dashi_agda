#!/usr/bin/env python3
"""Audit the PNF numeric ABI surface across Python and Agda text.

This is a static inspection helper only. It does not invoke Agda or import the
sibling repository. The script compares the Python ABI surface described by
``itir_mcp.pnf_numeric_abi`` against the requested Agda module path if present
and reports covered versus missing names.
"""

from __future__ import annotations

import argparse
import ast
import json
import re
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any


REPO_ROOT = Path(__file__).resolve().parents[1]
DEFAULT_PYTHON_PATH = (
    REPO_ROOT.parent / "ITIR-suite" / "itir-mcp" / "src" / "itir_mcp" / "pnf_numeric_abi.py"
)
DEFAULT_SPECTRAL_PYTHON_PATH = (
    REPO_ROOT.parent
    / "ITIR-suite"
    / "itir-mcp"
    / "src"
    / "itir_mcp"
    / "pnf_spectral_numeric_abi.py"
)
DEFAULT_AGDA_PATH = REPO_ROOT / "DASHI" / "Interop" / "PNFSpectralNumericABICore.agda"
DEFAULT_ODD_GRASSMANN_AGDA_PATH = REPO_ROOT / "DASHI" / "Core" / "OddGrassmannLaneCore.agda"
DEFAULT_EVEN_LANE_AGDA_PATH = REPO_ROOT / "DASHI" / "Core" / "EvenLaneOperatorCore.agda"
DEFAULT_PARITY_AGDA_PATH = REPO_ROOT / "DASHI" / "Core" / "ParityLaneOperatorCore.agda"
DEFAULT_TRIT_AGDA_PATH = (
    REPO_ROOT / "DASHI" / "Algebra" / "Trit" / "OddEvenLaneTritBridge.agda"
)
DEFAULT_EIGEN_AGDA_PATH = REPO_ROOT / "DASHI" / "Core" / "ParityLaneEigenOperatorCore.agda"
DEFAULT_LANE369_AGDA_PATH = REPO_ROOT / "DASHI" / "Interop" / "OddEvenLane369Bridge.agda"


PAYLOAD_GET_RE = re.compile(r'payload\.get\("([^"]+)"\)')
TOP_LEVEL_SIG_RE = re.compile(r"(?m)^([A-Za-z][A-Za-z0-9']*)\s*:")
TOP_LEVEL_DECL_RE = re.compile(r"(?m)^(?:data|record|postulate)\s+([A-Za-z][A-Za-z0-9']*)\b")
AGDA_NAME_SIG_RE = re.compile(r"(?m)^\s+([A-Za-z][A-Za-z0-9']*)\s*:")
MODULE_RE = re.compile(r"(?m)^module\s+([A-Za-z][A-Za-z0-9'.]*)\s+where\b")


EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "A": ("gemvMatrixA", "PNFGEMVPayload"),
    "SCHEMA": ("PNFGEMVPayload",),
    "_vector": ("PNFGEMVPayload",),
    "b": ("gemvVectorB", "PNFGEMVPayload"),
    "cols": ("gemvCols", "PNFGEMVPayload"),
    "cpu_gemv": ("PNFGEMVPayload", "canonicalPNFGEMVPayloadCandidateOnlyIsTrue"),
    "dtype": ("gemvDType", "PNFGEMVPayload"),
    "parity_hash": ("gemvParityHash", "PNFGEMVPayload"),
    "rows": ("gemvRows", "PNFGEMVPayload"),
    "row_map": ("PNFRowMapBinding", "PNFGEMVPayload"),
    "schema": ("PNFGEMVPayload",),
    "validate_numeric_abi": ("PNFAdmissionRule", "canonicalPNFAdmissionRuleCandidateOnlyIsTrue"),
    "z": ("gemvVectorZ", "PNFGEMVPayload"),
}

SPECTRAL_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "SCHEMA": ("spectralSchemaV02", "PNFSpectralNumericABICoreReceipt"),
    "adjacency": ("adjacencyTable", "PNFAdjacencyABI"),
    "authority": ("authorityGate", "PNFAuthorityBoundaryLemmas"),
    "degree": ("degreeTable", "PNFAdjacencyABI"),
    "gemv": ("PNFGEMVPayload",),
    "graph_version": ("graphVersion", "PNFSpectralNumericABICoreReceipt"),
    "laplacian": ("laplacianTable", "PNFLaplacianABI"),
    "object_registry": ("objectRegistry", "PNFRowMapBinding"),
    "operator_profile": ("operatorProfile", "PNFLaplacianABI"),
    "parity_hash": ("gemvParityHash", "PNFGEMVPayload"),
    "phi": ("phiTable", "PhiCoordinateTable", "PNFEigenSpectralCoordinateABI"),
    "psi": ("psiTable", "PsiProbeTable"),
    "rebuild_witness": ("rebuildWitness", "PNFRebuildWitness"),
    "receipts": ("PNFAdmissionRule",),
    "residual_edge_table": ("residualEdgeTable", "PNFResidualEdgeTableABI"),
    "row_map": ("PNFRowMapBinding",),
    "schema": ("spectralSchemaV02",),
    "spectral_coordinates": ("phiTable", "psiTable", "PNFEigenSpectralCoordinateABI"),
    "validate_authority_gate": ("PNFAuthorityBoundaryLemmas", "authorityGate"),
    "validate_rebuild_witness": ("PNFRebuildWitness", "rebuildWitness"),
    "validate_spectral_numeric_abi": ("PNFAdmissionRule",),
}

ODD_GRASSMANN_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "authorityGate": ("authorityGate",),
    "candidateOnly": ("candidateOnly",),
    "nilpotentWitness": ("nilpotentWitness",),
    "oddCoeff": ("oddCoeff",),
    "oddDerivative": ("oddDerivative",),
    "oddIntegral": ("oddIntegral",),
    "oddMeasure": ("oddMeasure",),
    "oddProbe": ("oddProbe",),
    "residualWitness": ("residualWitness",),
}

EVEN_LANE_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "evenDerivative": ("derivative", "evenDerivative"),
    "evenIntegral": ("integral", "evenIntegral"),
}

PARITY_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "laneClass": ("LaneClass", "laneClassLabel", "receiptClass"),
    "oddCollapsedLane": ("oddCollapsedLane",),
    "evenSeparatedLane": ("evenSeparatedLane",),
    "unresolvedLane": ("unresolvedLane",),
}

TRIT_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "laneClassTrit": ("laneClassToTrit", "OddEvenLaneTritReceipt"),
    "tritCarrierBridgeSurface": ("OddEvenLaneTritReceipt",),
}

EIGEN_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "LaneEigenSurface": ("LaneEigenSurface", "canonicalOddLaneEigenSurface"),
    "HeckeLaneActionSurface": ("HeckeLaneActionSurface", "canonicalOddHeckeLaneActionSurface"),
}

LANE369_EXPECTED_BINDINGS: dict[str, tuple[str, ...]] = {
    "lane369Receipt": ("OddEvenLane369Receipt", "canonicalOddEvenLane369Receipt"),
    "lane369Surface": ("OddEvenLane369Receipt",),
    "canonicalLane369Receipt": ("canonicalOddEvenLane369Receipt",),
}


@dataclass
class Surface:
    present: bool
    path: str
    names: list[str] = field(default_factory=list)
    notes: list[str] = field(default_factory=list)
    module_name: str | None = None


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--python-path", type=Path, default=DEFAULT_PYTHON_PATH)
    parser.add_argument("--spectral-python-path", type=Path, default=DEFAULT_SPECTRAL_PYTHON_PATH)
    parser.add_argument("--agda-path", type=Path, default=DEFAULT_AGDA_PATH)
    parser.add_argument(
        "--odd-grassmann-agda-path",
        type=Path,
        default=DEFAULT_ODD_GRASSMANN_AGDA_PATH,
    )
    parser.add_argument("--even-lane-agda-path", type=Path, default=DEFAULT_EVEN_LANE_AGDA_PATH)
    parser.add_argument("--parity-agda-path", type=Path, default=DEFAULT_PARITY_AGDA_PATH)
    parser.add_argument("--trit-agda-path", type=Path, default=DEFAULT_TRIT_AGDA_PATH)
    parser.add_argument("--eigen-agda-path", type=Path, default=DEFAULT_EIGEN_AGDA_PATH)
    parser.add_argument("--lane369-agda-path", type=Path, default=DEFAULT_LANE369_AGDA_PATH)
    parser.add_argument(
        "--phi-psi-agda-path",
        type=Path,
        default=REPO_ROOT / "DASHI" / "Interop" / "PNFSpectralPhiPsiABICore.agda",
    )
    parser.add_argument("--limit", type=int, default=24, help="Max names shown per list.")
    parser.add_argument("--json-only", action="store_true", help="Print only the JSON payload.")
    return parser.parse_args()


def rel(path: Path) -> str:
    try:
        return path.relative_to(REPO_ROOT).as_posix()
    except ValueError:
        return str(path)


def read_text(path: Path) -> str | None:
    try:
        return path.read_text(encoding="utf-8")
    except OSError:
        return None


def unique(items: list[str]) -> list[str]:
    seen: set[str] = set()
    out: list[str] = []
    for item in items:
        if item in seen:
            continue
        seen.add(item)
        out.append(item)
    return out


def collect_python_surface(path: Path) -> Surface:
    text = read_text(path)
    if text is None:
        return Surface(
            present=False,
            path=rel(path),
            notes=["python source not readable"],
        )

    tree = ast.parse(text, filename=str(path))
    names: list[str] = []
    notes: list[str] = []

    for node in tree.body:
        if isinstance(node, ast.Assign):
            for target in node.targets:
                if isinstance(target, ast.Name):
                    names.append(target.id)
        elif isinstance(node, ast.AnnAssign) and isinstance(node.target, ast.Name):
            names.append(node.target.id)
        elif isinstance(node, ast.FunctionDef):
            names.append(node.name)

    class RuntimeFieldVisitor(ast.NodeVisitor):
        def __init__(self) -> None:
            self.fields: list[str] = []

        def visit_Call(self, node: ast.Call) -> None:
            if isinstance(node.func, ast.Attribute) and node.func.attr == "get":
                value = node.func.value
                if isinstance(value, ast.Name) and value.id == "payload":
                    if node.args and isinstance(node.args[0], ast.Constant) and isinstance(node.args[0].value, str):
                        self.fields.append(node.args[0].value)
            self.generic_visit(node)

        def visit_Dict(self, node: ast.Dict) -> None:
            for key in node.keys:
                if isinstance(key, ast.Constant) and isinstance(key.value, str):
                    self.fields.append(key.value)
            self.generic_visit(node)

    visitor = RuntimeFieldVisitor()
    visitor.visit(tree)

    names.extend(visitor.fields)
    names = unique(names)
    notes.append("static AST scan of module-level names and payload dict fields")

    return Surface(present=True, path=rel(path), names=sorted(names), notes=notes)


def collect_agda_surface(path: Path) -> Surface:
    text = read_text(path)
    if text is None:
        return Surface(
            present=False,
            path=rel(path),
            notes=["Agda module file missing or unreadable"],
        )

    names: list[str] = []
    module_match = MODULE_RE.search(text)
    module_name = module_match.group(1) if module_match else None
    names.extend(TOP_LEVEL_SIG_RE.findall(text))
    names.extend(TOP_LEVEL_DECL_RE.findall(text))
    names.extend(AGDA_NAME_SIG_RE.findall(text))
    names = unique(names)

    return Surface(
        present=True,
        path=rel(path),
        names=sorted(names),
        notes=["static text scan of top-level signatures and declarations"],
        module_name=module_name,
    )


def merge_surfaces(surfaces: list[Surface], label: str) -> Surface:
    present = any(surface.present for surface in surfaces)
    names: list[str] = []
    notes: list[str] = [f"{label} merged surface"]
    paths: list[str] = []
    for surface in surfaces:
        paths.append(surface.path)
        names.extend(surface.names)
        notes.extend(surface.notes)
    return Surface(
        present=present,
        path=", ".join(paths),
        names=sorted(unique(names)),
        notes=unique(notes),
    )


def build_report(
    py_surface: Surface,
    agda_surface: Surface,
    limit: int,
    expected_bindings: dict[str, tuple[str, ...]] | None = None,
) -> dict[str, Any]:
    shared = sorted(set(py_surface.names) & set(agda_surface.names))
    missing_from_agda = sorted(set(py_surface.names) - set(agda_surface.names))
    covered = shared
    agda_names = set(agda_surface.names)
    semantic_bindings: dict[str, list[str]] = {}
    semantic_missing: dict[str, list[str]] = {}
    bindings = expected_bindings if expected_bindings is not None else EXPECTED_BINDINGS

    for py_name in py_surface.names:
        expected = bindings.get(py_name, [])
        present = [name for name in expected if name in agda_names]
        missing = [name for name in expected if name not in agda_names]
        if present:
            semantic_bindings[py_name] = present
        if missing:
            semantic_missing[py_name] = missing

    return {
        "status": "ok" if agda_surface.present else "agda_missing",
        "python": {
            "present": py_surface.present,
            "path": py_surface.path,
            "names": py_surface.names[:limit],
            "count": len(py_surface.names),
            "notes": py_surface.notes,
        },
        "agda": {
            "present": agda_surface.present,
            "path": agda_surface.path,
            "names": agda_surface.names[:limit],
            "count": len(agda_surface.names),
            "notes": agda_surface.notes,
        },
        "coverage": {
            "shared": shared[:limit],
            "shared_count": len(shared),
            "covered": covered[:limit],
            "covered_count": len(covered),
            "missing_from_agda": missing_from_agda[:limit],
            "missing_from_agda_count": len(missing_from_agda),
            "semantic_bindings": dict(list(sorted(semantic_bindings.items()))[:limit]),
            "semantic_bindings_count": len(semantic_bindings),
            "semantic_missing": dict(list(sorted(semantic_missing.items()))[:limit]),
            "semantic_missing_count": len(semantic_missing),
        },
    }


def render_markdownish(report: dict[str, Any]) -> str:
    python_block = report["python"]
    agda_block = report["agda"]
    coverage = report["coverage"]

    lines = [
        "PNF numeric ABI surface audit",
        f"- python: {'present' if python_block['present'] else 'missing'} ({python_block['path']})",
        f"- agda: {'present' if agda_block['present'] else 'missing'} ({agda_block['path']})",
        f"- shared exact names: {coverage['shared_count']}",
        f"- semantic bindings: {coverage['semantic_bindings_count']}",
        f"- missing from agda: {coverage['missing_from_agda_count']}",
        f"- missing semantic bindings: {coverage['semantic_missing_count']}",
        "",
        "Covered:",
        "  " + (", ".join(coverage["covered"]) if coverage["covered"] else "none"),
        "Semantic bindings:",
        "  "
        + (
            "; ".join(
                f"{name} -> {', '.join(bindings)}"
                for name, bindings in coverage["semantic_bindings"].items()
            )
            if coverage["semantic_bindings"]
            else "none"
        ),
        "Missing:",
        "  " + (", ".join(coverage["missing_from_agda"]) if coverage["missing_from_agda"] else "none"),
        "Missing semantic bindings:",
        "  "
        + (
            "; ".join(
                f"{name} -> {', '.join(bindings)}"
                for name, bindings in coverage["semantic_missing"].items()
            )
            if coverage["semantic_missing"]
            else "none"
        ),
    ]
    return "\n".join(lines)


def main() -> int:
    args = parse_args()
    py_surface = collect_python_surface(args.python_path)
    spectral_py_surface = collect_python_surface(args.spectral_python_path)
    agda_surface = collect_agda_surface(args.agda_path)
    odd_grassmann_agda_surface = collect_agda_surface(args.odd_grassmann_agda_path)
    even_lane_agda_surface = collect_agda_surface(args.even_lane_agda_path)
    parity_agda_surface = collect_agda_surface(args.parity_agda_path)
    trit_agda_surface = collect_agda_surface(args.trit_agda_path)
    eigen_agda_surface = collect_agda_surface(args.eigen_agda_path)
    lane369_agda_surface = collect_agda_surface(args.lane369_agda_path)
    phi_psi_agda_surface = collect_agda_surface(args.phi_psi_agda_path)
    merged_py_surface = merge_surfaces([py_surface, spectral_py_surface], "python")
    merged_agda_surface = merge_surfaces(
        [
            agda_surface,
            odd_grassmann_agda_surface,
            even_lane_agda_surface,
            parity_agda_surface,
            trit_agda_surface,
            eigen_agda_surface,
            lane369_agda_surface,
            phi_psi_agda_surface,
        ],
        "agda",
    )
    expected_bindings = (
        EXPECTED_BINDINGS
        | SPECTRAL_EXPECTED_BINDINGS
        | ODD_GRASSMANN_EXPECTED_BINDINGS
        | EVEN_LANE_EXPECTED_BINDINGS
        | PARITY_EXPECTED_BINDINGS
        | TRIT_EXPECTED_BINDINGS
        | EIGEN_EXPECTED_BINDINGS
        | LANE369_EXPECTED_BINDINGS
    )
    report = build_report(
        merged_py_surface,
        merged_agda_surface,
        args.limit,
        expected_bindings,
    )
    report["python_v0_1"] = {
        "present": py_surface.present,
        "path": py_surface.path,
        "count": len(py_surface.names),
    }
    report["python_v0_2"] = {
        "present": spectral_py_surface.present,
        "path": spectral_py_surface.path,
        "count": len(spectral_py_surface.names),
    }
    report["agda_numeric_core"] = {
        "present": agda_surface.present,
        "path": agda_surface.path,
        "count": len(agda_surface.names),
    }
    report["agda_phi_psi_core"] = {
        "present": phi_psi_agda_surface.present,
        "path": phi_psi_agda_surface.path,
        "count": len(phi_psi_agda_surface.names),
    }
    report["agda_odd_grassmann_core"] = {
        "present": odd_grassmann_agda_surface.present,
        "path": odd_grassmann_agda_surface.path,
        "count": len(odd_grassmann_agda_surface.names),
    }
    report["agda_even_lane_core"] = {
        "present": even_lane_agda_surface.present,
        "path": even_lane_agda_surface.path,
        "count": len(even_lane_agda_surface.names),
    }
    report["agda_parity_core"] = {
        "present": parity_agda_surface.present,
        "path": parity_agda_surface.path,
        "count": len(parity_agda_surface.names),
    }
    report["agda_trit_core"] = {
        "present": trit_agda_surface.present,
        "path": trit_agda_surface.path,
        "count": len(trit_agda_surface.names),
    }
    report["agda_eigen_core"] = {
        "present": eigen_agda_surface.present,
        "path": eigen_agda_surface.path,
        "count": len(eigen_agda_surface.names),
    }
    report["agda_lane369_core"] = {
        "present": lane369_agda_surface.present,
        "path": lane369_agda_surface.path,
        "count": len(lane369_agda_surface.names),
    }

    if args.json_only:
        print(json.dumps(report, indent=2, sort_keys=True))
    else:
        print(json.dumps(report, indent=2, sort_keys=True))
        print()
        print(render_markdownish(report))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
