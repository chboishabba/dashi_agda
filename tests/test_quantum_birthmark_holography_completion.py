from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_holographic_same_object_owner_names_exact_upstream_gap():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicSameObjectWeldExact.agda")
    assert "treeEntanglementEntropy" in p
    assert "holographicContract" in p
    assert "ryuTakayanagiAreaLawShapeOwned" in p
    assert "densityMatrixEntropyWeldRequired" in p
    assert "sameObjectBoundaryEntropyCompiler" in p
    assert "areaLawDoesNotComputeVonNeumannEntropyOfContract" in p


def test_area_capacity_reuses_all_existing_holography_owners():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicCapacityExact.agda")
    assert "UVFinitenessTheorem" in p
    assert "areaBoundImpliesUVFinite" in p
    assert "DASHI.Physics.Holography.AreaLaw" in p
    assert "UVFinitenessHolographyInstance" in p
    assert "areaLawUV" in p
    assert "AgreementDepth-theorem" in p
    assert "agreementDepthDoesNotWeldAreaBoundToUVBounded" in p
    assert "areaCapacityDoesNotDetermineBirthmarkValue" in p
    assert "areaCapacityDoesNotDetermineResidualInformationDensity" in p


def test_lorentz_horizon_bridge_keeps_jacobson_payment_explicit():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicLorentz31JacobsonBridgeExact.agda")
    assert "LargePosetContinuumLorentz31Authority" in p
    assert "QuantumMereologySpacetimePromotionExact" in p
    assert "SpacetimeSheafObligation" in p
    assert "timeDimensionIsOne" in p
    assert "localHorizonAttachment" in p
    assert "clausiusRelation" in p
    assert "entropyAreaVariationWeld" in p
    assert "sameSpatialCarrier" in p
    assert "einsteinEquationNotDerivedByThisAdapter" in p
    assert "birthmarkDoesNotSupplyClausiusRelation" in p


def test_quantum_rollup_registers_completion_owners():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicSameObjectWeldExact" in p
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicCapacityExact" in p
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicLorentz31JacobsonBridgeExact" in p
