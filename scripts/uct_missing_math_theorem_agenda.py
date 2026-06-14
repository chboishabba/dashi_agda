#!/usr/bin/env python3
"""Emit the fail-closed Paper 8 UCT theorem agenda.

The agenda is deliberately repo-local and stdlib-only.  It encodes the exact
UCT-A through UCT-H theorem packet and validates that the current Paper 8 docs
and Agda boundary surfaces still contain the markers this packet depends on.
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any


REQUIRED_SOURCE_FILES = (
    "Docs/support/reference/UnifiedRoutesLanePlan.md",
    "Docs/support/reference/AgdaValidationTargets.md",
    "Docs/support/reference/CurrentGateStatus.md",
    "Docs/support/reference/FinalAnalyticWalls.md",
    "Docs/papers/live/Paper8UnificationDraft.md",
    "Docs/papers/generated/core_papers_theorem_var_manifest.json",
    "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda",
    "DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda",
    "DASHI/Physics/Closure/UnificationGluingCrossTermNullClassBoundary.agda",
    "DASHI/Physics/Closure/UnificationNullClassStabilityBoundary.agda",
    "DASHI/Physics/Closure/UnificationNullToQuotientEqualityTransportBoundary.agda",
    "DASHI/Physics/Closure/UnificationGluingModuloNullLinearityCompositeBoundary.agda",
    "DASHI/Physics/Closure/UnificationModuloNullLinearityFromCrossTermNullityBoundary.agda",
    "DASHI/Physics/Closure/UnificationFourPointCancellationFromCrossTermNullityBoundary.agda",
    "DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda",
    "DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda",
)

REQUIRED_MARKERS: dict[str, tuple[str, ...]] = {
    "Docs/support/reference/UnifiedRoutesLanePlan.md": (
        "residual PDE specification, ellipticity class, Carleman intake, and then the",
        "The repo may also record the exact downstream `UCT.5-UCT.8` consumer chain",
        "The live theorem wall is still `UCT.1-UCT.4`",
    ),
    "Docs/support/reference/AgdaValidationTargets.md": (
        "Cross-term nullity must feed modulo-null linearity, four-point cancellation,",
        "Authority packet surfaces stay fail-closed",
    ),
    "Docs/support/reference/CurrentGateStatus.md": (
        "explicit candidate `UCT.1-UCT.8`",
        "`UCT.1-UCT.4`",
    ),
    "Docs/support/reference/FinalAnalyticWalls.md": (
        "candidate `UCT.1-UCT.8`",
        "`UCT.1-UCT.4` wall",
    ),
    "Docs/papers/live/Paper8UnificationDraft.md": (
        "cross-term nullity frontier",
        "JvN recovery",
        "terminal unification guard remains false",
    ),
    "Docs/papers/generated/core_papers_theorem_var_manifest.json": (
        "uct1ResidualPDESpecificationRecorded",
        "uct2EllipticityOrParabolicityClassRecorded",
        "uct3CarlemanUniqueContinuationRecorded",
        "uct4ActualTheoremTargetRecorded",
        "moduloNullLinearityConsumer",
        "fourPointConsumer",
        "parallelogramConsumer",
        "jordanVonNeumannAdapterConsumer",
    ),
    "DASHI/Physics/Closure/UnificationCrossTermNullityTheoremBoundary.agda": (
        "UCT1-residualPDESpecificationClause",
        "UCT2-ellipticityOrParabolicityClassClause",
        "UCT3-CarlemanUniqueContinuationIntakeClause",
        "UCT4-crossTermNullityTheoremClause",
        "UCT5-moduloNullLinearityConsumerClause",
        "UCT6-fourPointCancellationConsumerClause",
        "UCT7-parallelogramConsumerClause",
        "UCT8-jordanVonNeumannAdapterConsumerClause",
        "terminalPromotion",
    ),
    "DASHI/Physics/Closure/UnificationCrossTermNullityDiscriminantBoundary.agda": (
        "liveCrossTermIntakeText",
        "explicitUCT4ToUCT8ChainText",
        "UnificationCrossTermNullityDiscriminantProved = false",
    ),
    "DASHI/Physics/Closure/UnificationGluingCrossTermNullClassBoundary.agda": (
        "crossTermExpressionRecorded",
        "crossTermNullClassTheoremProved",
    ),
    "DASHI/Physics/Closure/UnificationNullClassStabilityBoundary.agda": (
        "nullPredicateToQuotientEqualityTransportProved",
        "representativeInvarianceProved",
    ),
    "DASHI/Physics/Closure/UnificationNullToQuotientEqualityTransportBoundary.agda": (
        "crossTermNullToModuloLinearityProved",
        "nullToZeroBridgeProved",
    ),
    "DASHI/Physics/Closure/UnificationGluingModuloNullLinearityCompositeBoundary.agda": (
        "moduloNullGluingLinearityProved",
        "actualFourPointCancellationProved",
        "terminalUnificationPromotion",
    ),
    "DASHI/Physics/Closure/UnificationModuloNullLinearityFromCrossTermNullityBoundary.agda": (
        "cross-term nullity",
        "modulo-null gluing linearity",
        "four-point cancellation route",
    ),
    "DASHI/Physics/Closure/UnificationFourPointCancellationFromCrossTermNullityBoundary.agda": (
        "fourPointCancellationProved",
        "parallelogramConsumerRecorded",
        "terminalUnificationPromotion",
    ),
    "DASHI/Physics/Closure/UnificationParallelogramFromBilinearBoundary.agda": (
        "parallelogram",
        "jordanVonNeumannRouteFed",
    ),
    "DASHI/Physics/Closure/UnificationParallelogramToJordanVonNeumannSocketCompositeLightweightBoundary.agda": (
        "uct8TheoremWallEntryText",
        "UCT.4 cross-term nullity -> UCT.5 modulo-null -> UCT.6 four-point -> UCT.7 parallelogram",
        "UnificationParallelogramToJordanVonNeumannSocketCompositeProved = false",
    ),
}

ALLOWED_STATUSES = {"open", "authority-intake", "downstream-locked"}


def theorem(
    theorem_id: str,
    canonical_uct: str,
    title: str,
    statement: str,
    symbolic_conclusion: str,
    required_inputs: list[str],
    dependencies: list[str],
    downstream_unlocks: list[str],
    status: str,
    evidence_markers: list[str],
) -> dict[str, Any]:
    if status not in ALLOWED_STATUSES:
        raise ValueError(f"{theorem_id}: invalid status {status!r}")
    return {
        "id": theorem_id,
        "canonical_uct": canonical_uct,
        "title": title,
        "theorem_statement": statement,
        "symbolic_conclusion": symbolic_conclusion,
        "required_inputs": required_inputs,
        "dependencies": dependencies,
        "downstream_unlocks": downstream_unlocks,
        "status": status,
        "promotion_allowed": False,
        "terminal_promotion": False,
        "evidence_markers": evidence_markers,
    }


def build_agenda() -> dict[str, Any]:
    targets = [
        theorem(
            "UCT-A",
            "UCT.1",
            "OverlapResidualPDE",
            "Specify the exact overlap residual PDE satisfied by c(s1,s2)=G(s1 +V s2) -V G(s1) -V G(s2), including domain, boundary, quotient, and lane parameters.",
            "ResidualPDE(c) = 0 is a typed theorem target, not an inferred consequence of two-homogeneity.",
            [
                "admissible defect quotient V/null",
                "gluing operator G and cross-term c(s1,s2)",
                "lane-specific overlap residual construction",
                "domain and boundary-condition bookkeeping",
            ],
            [],
            ["UCT-B", "UCT-C", "UCT-D"],
            "open",
            [
                "uct1ResidualPDESpecificationRecorded",
                "UCT1-residualPDESpecificationClause",
                "residualPDEHypothesesSpecified",
            ],
        ),
        theorem(
            "UCT-B",
            "UCT.2",
            "EllipticityWitness",
            "Provide the elliptic or parabolic operator-class witness for the UCT-A residual PDE in the exact unique-continuation regime consumed by Paper 8.",
            "OperatorClass(ResidualPDE(c)) in {elliptic, parabolic} with admissible coefficients and boundary data.",
            [
                "UCT-A residual PDE statement",
                "coefficient regularity and degeneracy bounds",
                "lane-specific elliptic/parabolic classification",
            ],
            ["UCT-A"],
            ["UCT-C", "UCT-D"],
            "open",
            [
                "uct2EllipticityOrParabolicityClassRecorded",
                "UCT2-ellipticityOrParabolicityClassClause",
                "ellipticityOrParabolicityClassSpecified",
            ],
        ),
        theorem(
            "UCT-C",
            "UCT.3",
            "CarlemanUniqueContinuation",
            "Import or prove the Carleman/unique-continuation theorem matched to UCT-B and strong enough to force the overlap residual into the null class.",
            "CarlemanUC(ResidualPDE(c), OperatorClass) => nullClass(c).",
            [
                "UCT-A residual PDE statement",
                "UCT-B operator-class witness",
                "matched Carleman or unique-continuation authority",
                "vanishing/smallness hypotheses in the recorded quotient geometry",
            ],
            ["UCT-A", "UCT-B"],
            ["UCT-D"],
            "authority-intake",
            [
                "uct3CarlemanUniqueContinuationRecorded",
                "UCT3-CarlemanUniqueContinuationIntakeClause",
                "carlemanHypothesesSpecified",
            ],
        ),
        theorem(
            "UCT-D",
            "UCT.4",
            "CrossTermNullity",
            "Prove that the gluing overlap cross-term is null for every pair of admissible sections.",
            "forall s1 s2, nullClass(G(s1 +V s2) -V G(s1) -V G(s2)).",
            [
                "UCT-A residual PDE statement",
                "UCT-B ellipticity/parabolicity witness",
                "UCT-C Carleman/unique-continuation intake",
                "representative invariance and null-stability transport",
            ],
            ["UCT-A", "UCT-B", "UCT-C"],
            ["UCT-E", "UCT-F", "UCT-G", "UCT-H"],
            "open",
            [
                "uct4ActualTheoremTargetRecorded",
                "UCT4-crossTermNullityTheoremClause",
                "crossTermNullityTheoremProved",
            ],
        ),
        theorem(
            "UCT-E",
            "UCT.5",
            "ModuloNullLinearity",
            "Derive modulo-null gluing linearity from UCT-D through fail-closed null-to-quotient transport.",
            "[G(s1 +V s2)] = [G(s1)] + [G(s2)] in V/null.",
            [
                "UCT-D cross-term nullity",
                "null-to-quotient equality transport",
                "representative-invariance proof",
                "quotient operation well-definedness",
            ],
            ["UCT-D"],
            ["UCT-F", "UCT-G", "UCT-H"],
            "downstream-locked",
            [
                "moduloNullLinearityConsumer",
                "UCT5-moduloNullLinearityConsumerClause",
                "moduloNullGluingLinearityProved",
            ],
        ),
        theorem(
            "UCT-F",
            "UCT.6",
            "FourPointCancellation",
            "Convert UCT-E modulo-null linearity into the four-point cancellation identity required by the quotient norm grammar.",
            "Q(x+y) + Q(x-y) - 2Q(x) - 2Q(y) = 0 on V/null.",
            [
                "UCT-D cross-term nullity",
                "UCT-E modulo-null linearity",
                "polarization/four-point residual surface",
                "additive test-functional invariance",
            ],
            ["UCT-D", "UCT-E"],
            ["UCT-G", "UCT-H"],
            "downstream-locked",
            [
                "fourPointConsumer",
                "UCT6-fourPointCancellationConsumerClause",
                "fourPointCancellationProved",
            ],
        ),
        theorem(
            "UCT-G",
            "UCT.7",
            "ParallelogramLaw",
            "Derive the parallelogram law on the quotient norm from UCT-F and the recorded bilinear/parallelogram socket.",
            "||x+y||^2 + ||x-y||^2 = 2||x||^2 + 2||y||^2 on V/null.",
            [
                "UCT-D cross-term nullity",
                "UCT-E modulo-null linearity",
                "UCT-F four-point cancellation",
                "quotient norm/squared-norm compatibility",
            ],
            ["UCT-D", "UCT-E", "UCT-F"],
            ["UCT-H"],
            "downstream-locked",
            [
                "parallelogramConsumer",
                "UCT7-parallelogramConsumerClause",
                "parallelogramProved",
            ],
        ),
        theorem(
            "UCT-H",
            "UCT.8",
            "JordanVonNeumannRecovery",
            "Recover the Paper 8 quotient inner product from UCT-G using the Jordan-von Neumann polarization route, without terminal promotion.",
            "<x,y> = (1/4)(||x+y||^2 - ||x-y||^2) on V/null, with Hilbert recovery scoped to the quotient.",
            [
                "UCT-D cross-term nullity",
                "UCT-G parallelogram law",
                "null-space quotient hypotheses",
                "Jordan-von Neumann adapter authority/socket",
            ],
            ["UCT-D", "UCT-G"],
            [],
            "downstream-locked",
            [
                "jordanVonNeumannAdapterConsumer",
                "UCT8-jordanVonNeumannAdapterConsumerClause",
                "uct8TheoremWallEntryText",
            ],
        ),
    ]
    return {
        "schema": "dashi.paper8_uct_missing_math_theorem_agenda.v1",
        "ok": True,
        "fail_closed": True,
        "paper": "Paper8 Unification",
        "promotion_allowed": False,
        "terminal_promotion": False,
        "source_files": list(REQUIRED_SOURCE_FILES),
        "theorem_targets": targets,
    }


def validate_agenda(repo_root: Path, agenda: dict[str, Any]) -> None:
    errors: list[str] = []
    target_ids = [target["id"] for target in agenda["theorem_targets"]]
    expected_ids = [f"UCT-{letter}" for letter in "ABCDEFGH"]
    if target_ids != expected_ids:
        errors.append(f"expected theorem ids {expected_ids}, got {target_ids}")

    target_id_set = set(target_ids)
    for target in agenda["theorem_targets"]:
        for dep in target["dependencies"]:
            if dep not in target_id_set:
                errors.append(f"{target['id']}: unknown dependency {dep}")
        for unlock in target["downstream_unlocks"]:
            if unlock not in target_id_set:
                errors.append(f"{target['id']}: unknown downstream unlock {unlock}")
        if target["status"] not in ALLOWED_STATUSES:
            errors.append(f"{target['id']}: invalid status {target['status']}")
        if target["promotion_allowed"] is not False:
            errors.append(f"{target['id']}: promotion_allowed must be false")
        if target["terminal_promotion"] is not False:
            errors.append(f"{target['id']}: terminal_promotion must be false")

    locked_ids = {"UCT-E", "UCT-F", "UCT-G", "UCT-H"}
    for target in agenda["theorem_targets"]:
        if target["id"] in locked_ids:
            if target["status"] != "downstream-locked":
                errors.append(f"{target['id']}: must be downstream-locked")
            if "UCT-D" not in target["dependencies"]:
                errors.append(f"{target['id']}: must depend on UCT-D")

    if agenda.get("ok") is not True:
        errors.append("top-level ok must be true")
    if agenda.get("fail_closed") is not True:
        errors.append("top-level fail_closed must be true")
    if agenda.get("promotion_allowed") is not False:
        errors.append("top-level promotion_allowed must be false")
    if agenda.get("terminal_promotion") is not False:
        errors.append("top-level terminal_promotion must be false")

    missing_files = [path for path in REQUIRED_SOURCE_FILES if not (repo_root / path).is_file()]
    for path in missing_files:
        errors.append(f"missing required source file: {path}")

    for rel_path, markers in REQUIRED_MARKERS.items():
        path = repo_root / rel_path
        if not path.is_file():
            continue
        text = path.read_text(encoding="utf-8")
        for marker in markers:
            if marker not in text:
                errors.append(f"{rel_path}: missing marker {marker!r}")

    if errors:
        raise SystemExit("fail-closed UCT agenda validation failed:\n" + "\n".join(f"  - {e}" for e in errors))


def escape_cell(value: Any) -> str:
    if isinstance(value, list):
        text = ", ".join(str(item) for item in value) if value else "-"
    elif isinstance(value, bool):
        text = "true" if value else "false"
    else:
        text = str(value)
    return text.replace("|", "\\|").replace("\n", " ")


def render_markdown(agenda: dict[str, Any]) -> str:
    columns = (
        "id",
        "canonical_uct",
        "title",
        "status",
        "theorem_statement",
        "symbolic_conclusion",
        "required_inputs",
        "dependencies",
        "downstream_unlocks",
        "promotion_allowed",
        "terminal_promotion",
    )
    lines = [
        "# Paper 8 UCT Missing-Math Theorem Agenda",
        "",
        "Policy: ok=true; fail_closed=true; promotion_allowed=false; terminal_promotion=false.",
        "",
        "| " + " | ".join(columns) + " |",
        "| " + " | ".join("---" for _ in columns) + " |",
    ]
    for target in agenda["theorem_targets"]:
        lines.append("| " + " | ".join(escape_cell(target[column]) for column in columns) + " |")
    return "\n".join(lines) + "\n"


def parse_args() -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--repo-root", type=Path, default=Path.cwd())
    parser.add_argument("--format", choices=("json", "md"), default="json")
    return parser.parse_args()


def main() -> int:
    args = parse_args()
    repo_root = args.repo_root.resolve()
    agenda = build_agenda()
    validate_agenda(repo_root, agenda)
    if args.format == "md":
        sys.stdout.write(render_markdown(agenda))
    else:
        sys.stdout.write(json.dumps(agenda, indent=2, sort_keys=True) + "\n")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
