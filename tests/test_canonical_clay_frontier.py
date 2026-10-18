from __future__ import annotations

import re
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
FRONTIER = ROOT / "DASHI/Physics/CanonicalClayFrontierExact.agda"


def _read() -> str:
    return FRONTIER.read_text(encoding="utf-8")


def _imports(text: str) -> str:
    return "\n".join(
        line for line in text.splitlines()
        if line.lstrip().startswith(("import ", "open import "))
    )


def test_unified_frontier_is_safe_round_free_and_qualified_only():
    text = _read()
    imports = _imports(text)
    assert "{-# OPTIONS --safe #-}" in text
    assert "{!!}" not in text
    assert "--allow-unsolved-metas" not in text
    assert not re.search(r"(?m)^\s*postulate\b", text)
    assert "Round" not in imports
    assert (
        "YangMillsCanonicalClayResidualExact as YM using ()" in imports
    )
    assert "NSCanonicalClayResidualExact as NS using ()" in imports


def test_unified_frontier_exposes_exact_yang_mills_live_obligations():
    text = _read()
    for name in [
        "cmp109SourceSemantics",
        "physicalTransferGap",
        "cmp116SelectedTermReplay",
        "cmp116TraceEntropyBudget",
    ]:
        assert name in text


def test_unified_frontier_exposes_exact_navier_stokes_live_obligations():
    text = _read()
    for name in [
        "a1PhysicalPopulation",
        "a2MajorantDomination",
        "a3Continuation",
        "b4PhysicalR440Payment",
        "b123PhysicalProducers",
        "b7IntegratedControl",
        "bContinuationInputs",
        "cdReleasedReconstruction",
    ]:
        assert name in text


def test_unified_frontier_is_failure_closed():
    text = _read()
    for literal in [
        "clayYangMillsPromoted = false",
        "clayNavierStokesPromoted = false",
        "clayPromotion = false",
        "unresolvedPackagesDischarged = false",
    ]:
        assert literal in text
    assert "nsUnresolvedPackages = 13716" in text


def test_unified_frontier_preserves_scheduler_gate_equalities():
    text = _read()
    for name in [
        "yangMillsSchedulerPromotionAgrees",
        "navierStokesSchedulerPromotionAgrees",
        "navierStokesUnresolvedGateAgrees",
    ]:
        assert name in text
