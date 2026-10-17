from __future__ import annotations

import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def _read(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def _import_lines(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("import ", "open import "))
    )


def _assert_safe_surface(text: str) -> None:
    assert "{-# OPTIONS --safe #-}" in text
    assert "{!!}" not in text
    assert "--allow-unsolved-metas" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)


def test_ns_canonical_root_is_concrete_nonround_run_target():
    data = json.loads(_read(".dashi/canonical-roots.json"))
    roots = data["roots"]
    assert "DASHI.Physics.Closure.NSConcreteLiteralClayABCDRunTargetExact" in roots
    assert "DASHI.Physics.Closure.NSLiteralClayABCDCapstone" not in roots
    assert "DASHI.Physics.Closure.NSClayOfficialSemanticPromotionBoundaryExact" not in roots
    assert data["policy"]["rounds_authoritative_by_default"] is False
    assert data["policy"]["body_only_equivalence_is_semantic_evidence"] is False


def test_literal_abcd_uses_nonround_forced_breakdown_coordinates():
    text = _read("DASHI/Physics/Closure/NSClayLiteralABCDExact.agda")
    imports = _import_lines(text)
    assert "NSClayForcedBreakdownSourceCoordinatesExact" in imports
    assert "NSTriadKNClayForcedBreakdownFormulationRound523Exact" not in imports


def test_forced_breakdown_coordinate_owner_is_safe_and_round_free():
    text = _read(
        "DASHI/Physics/Closure/NSClayForcedBreakdownSourceCoordinatesExact.agda"
    )
    _assert_safe_surface(text)
    assert "Round" not in _import_lines(text)
    for name in [
        "positiveViscosity",
        "rapidInitialSpatialDecay",
        "periodicInitialDatum",
        "rapidForcingSpaceTimeDecay",
        "rapidForcingTimeDecay",
        "boundedEnergyRequirement",
        "periodicSolutionRequirement",
        "requiredByC",
        "requiredByD",
    ]:
        assert name in text


def test_literal_abcd_preserves_forced_coordinate_checks():
    text = _read("DASHI/Physics/Closure/NSClayLiteralABCDExact.agda")
    for name in [
        "cRequiresPositiveViscosity",
        "cRequiresRapidInitialSpatialDecay",
        "cRequiresRapidForcingSpaceTimeDecay",
        "cRequiresBoundedEnergy",
        "dRequiresPositiveViscosity",
        "dRequiresPeriodicInitialDatum",
        "dRequiresRapidForcingTimeDecay",
        "dRequiresPeriodicSolution",
    ]:
        assert name in text
