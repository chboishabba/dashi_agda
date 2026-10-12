from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def text(path: str) -> str:
    return (ROOT / path).read_text(encoding="utf-8")


def test_null_contracted_relation_has_explicit_tensor_recovery_compiler():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonNullConeRecoveryExact.agda")
    assert "NullContractedFieldRelation" in p
    assert "NullConeTensorRigidity" in p
    assert "TensorEquationModuloMetric" in p
    assert "recoverTensorEquationModuloMetric" in p
    assert "nullRelationAloneDoesNotFixCosmologicalTerm" in p


def test_recovery_keeps_geometry_and_physics_payments_separate():
    p = text("DASHI/Quantum/QuantumBirthmarkJacobsonNullConeRecoveryExact.agda")
    assert "nullConeRigidityStillRequired" in p
    assert "stressEnergySameObjectStillRequired" in p
    assert "unruhClausiusStillRequired" in p
    assert "continuumRaychaudhuriStillRequired" in p
    assert "tensorRecoveryCompilerOwned" in p


def test_terminal_cutset_registers_reduced_null_direction_leaf():
    p = text("DASHI/Quantum/QuantumBirthmarkHolographyGravityTerminalCutsetExact.agda")
    assert "nullDirectionTensorRecoveryCompilerOwned" in p
    assert "nullConeRigidityTheoremStillRequired" in p


def test_quantum_rollup_registers_null_cone_recovery():
    p = text("DASHI/Quantum/Everything.agda")
    assert "import DASHI.Quantum.QuantumBirthmarkJacobsonNullConeRecoveryExact" in p
