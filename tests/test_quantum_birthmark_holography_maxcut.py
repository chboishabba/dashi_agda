from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_holography_bridge_reuses_existing_owners_and_keeps_firewalls():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyBridgeExact.agda")
    assert "HolographicBulkBoundaryReceipt" in p
    assert "UVFinitenessHolographyTests" in p
    assert "AdelicSpectralClaimStrengthAuditExact" in p
    assert "bulkBoundaryDictionaryDoesNotImplyEntropicGravity" in p
    assert "areaBoundDoesNotIdentifyEntropyOfSameBoundaryState" in p
    assert "birthmarkDoesNotImplyRyuTakayanagi" in p
    assert "holographicDictionaryDoesNotEraseBulkResidual" in p
    assert "boundarySufficiencyNeedsSameObjectWeld" in p


def test_cross_lane_status_names_the_real_residuals():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyBridgeExact.agda")
    assert "sameObjectBoundaryEntropyWeldStillRequired" in p
    assert "physicalBulkBoundaryDictionaryStillRequired" in p
    assert "entropyAreaGravityCompositionStillConditional" in p
    assert "pAdicDictionaryIsNotFourDimensionalSpacetimeHolography" in p


def test_quantum_rollup_imports_holography_bridge():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographyBridgeExact" in p
