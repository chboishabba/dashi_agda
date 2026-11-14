from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_upstream_tensor_network_audit_blocks_false_same_object_rt_promotion():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographicTensorNetworkAuditExact.agda")
    assert "holographicStateContractMismatch" in p
    assert "contractIgnoresPerfectTensorArgument" in p
    assert "canonicalQubitTensorIsometryIsNotStrongPerfectTensorReceipt" in p
    assert "rtTheoremIsDefinitionLevelAreaLaw" in p
    assert "upstreamRTNotDerivedFromConstructedBoundaryState" in p
    assert "correctedMaximallyEntangledCutModelRequired" in p
    assert "upstreamStateContractMismatchSourceWrittenInLean" in p
    assert "upstreamStateContractSameObjectImpossibleAsWritten" in p
    assert "upstreamDefinitionReplacementRequired" in p


def test_rollup_imports_tensor_network_audit():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkHolographicTensorNetworkAuditExact" in p
