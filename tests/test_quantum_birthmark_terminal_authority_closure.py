from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OWNER = ROOT / "DASHI/Quantum/QuantumBirthmarkTerminalAuthorityClosureExact.agda"
ROLLUP = ROOT / "DASHI/Quantum/Everything.agda"


def test_terminal_authority_closure_surface():
    text = OWNER.read_text()
    for needle in [
        "AuthoritySourceLedger",
        "terminalAuthorityClosureCompilerSourceWritten",
        "noFurtherFormalWeldDebt",
        "remainingWorkIsSourceInstantiationOrEmpiricalCalibration",
        "waldContinuumGRAuthorityRecorded",
        "modularBWKMSAuthoritySurfaceRecorded",
        "jacobson1995EquationOfStateAuthorityRecorded",
        "dorauMuch2026RelativeEntropyAuthorityRecorded",
        "correctedTreeReplacementContractSourceWritten",
    ]:
        assert needle in text


def test_rollup_registers_terminal_authority_closure():
    assert "QuantumBirthmarkTerminalAuthorityClosureExact" in ROLLUP.read_text()
