from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parents[1]
EVERYTHING = REPO_ROOT / "DASHI" / "Everything.agda"

MODULES = {
    "DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt": (
        REPO_ROOT / "DASHI" / "Physics" / "Closure" / "BothwellYe2022MillimetreRedshiftReceipt.agda"
    ),
    "DASHI.Physics.Closure.WolfPrize2026UltracoldControlBridge": (
        REPO_ROOT / "DASHI" / "Physics" / "Closure" / "WolfPrize2026UltracoldControlBridge.agda"
    ),
}


def read(path: Path) -> str:
    assert path.is_file(), f"missing {path.relative_to(REPO_ROOT)}"
    return path.read_text(encoding="utf-8")


def test_ultracold_redshift_modules_exist_and_keep_provenance_boundaries() -> None:
    redshift = read(MODULES["DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt"])
    wolf = read(MODULES["DASHI.Physics.Closure.WolfPrize2026UltracoldControlBridge"])

    for expected in (
        "10.1038/s41586-021-04349-7",
        "Nature 602, 420-424 (2022)",
        "single millimetre-scale sample",
        "7.6e-21",
        "linear frequency gradient consistent with gravitational redshift",
        "exactMillimetreCarrierClaimed =",
        "empiricalConsistencyPromotedToProofOfGR =",
        "requestFullyDischarged =",
    ):
        assert expected in redshift

    for expected in (
        "Immanuel F. Bloch",
        "Jun Ye",
        "Wolf Prize in Physics",
        "transformative, widely applicable advances in the control of ultracold atomic systems",
        "opticalLatticeQuantumSimulation",
        "opticalAtomicClockMetrology",
        "blochAndYeObservablesConflated =",
        "prizeCitationUsedAsPhysicsProof =",
    ):
        assert expected in wolf

    for forbidden in (
        "exactMillimetreCarrierClaimed = true",
        "empiricalConsistencyPromotedToProofOfGR = true",
        "requestFullyDischarged = true",
    ):
        assert forbidden not in redshift

    for forbidden in (
        "blochAndYeObservablesConflated = true",
        "prizeCitationUsedAsPhysicsProof = true",
    ):
        assert forbidden not in wolf


def test_ultracold_redshift_modules_attach_to_existing_clock_machinery() -> None:
    redshift = read(MODULES["DASHI.Physics.Closure.BothwellYe2022MillimetreRedshiftReceipt"])

    for owner in (
        "QuantumClockProperTimeRedshiftBridge",
        "QuantumClockDimensionlessObservableLaw",
        "QuantumClockEmpiricalRedshiftReceiptRequest",
    ):
        assert owner in redshift


def test_ultracold_redshift_modules_are_imported_once_by_everything() -> None:
    everything = read(EVERYTHING)
    for module in MODULES:
        line = f"import {module}"
        assert everything.count(line) == 1, f"expected one import of {module}"
