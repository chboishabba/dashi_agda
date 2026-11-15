from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_corrected_rt_owner_records_same_object_entangled_cut_theorem():
    p = text("DASHI/Quantum/QuantumBirthmarkCorrectedRTSameObjectExact.agda")
    assert "maxEntangledSchmidtDensity" in p
    assert "reducedDensityA_eq_uniformDiagonal" in p
    assert "reducedEntropy_eq_kLogTwo" in p
    assert "correctedRTSameObjectEntropy" in p
    assert "sameObjectEntropyAlgebraClosed" in p
    assert "upstreamZModCarrierFactorizationSourceWritten" in p
    assert "correctedEntangledStateOnUpstreamCarrierSourceWritten" in p
    assert "correctedUnbalancedRTForAdequateComplementSourceWritten" in p


def test_rt_owner_recuts_upstream_state_seam_as_definition_replacement():
    p = text("DASHI/Quantum/QuantumBirthmarkCorrectedRTSameObjectExact.agda")
    assert "upstreamStateContractSameObjectImpossibleAsWritten" in p
    assert "upstreamDefinitionReplacementRequired" in p
    assert "upstreamTreeContractionReplacementOrEquivalenceStillRequired" in p
    assert "minimalCutCarrierIdentificationStillRequired" in p
    assert "physicalBulkBoundaryDictionaryStillRequired" in p
    assert "correctedFiniteModelIsNotPhysicalAdSCFT" in p


def test_same_object_weld_reuses_corrected_rt_owner():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicSameObjectWeldExact.agda")
    assert "QuantumBirthmarkCorrectedRTSameObjectExact" in p
    assert "correctedFiniteRTEntropyWeldClosed" in p
    assert "upstreamStateCarrierWeldStillRequired" in p


def test_quantum_rollup_registers_corrected_rt_owner():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkCorrectedRTSameObjectExact" in p
