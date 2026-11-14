from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def read(rel: str) -> str:
    path = ROOT / rel
    assert path.is_file(), f"missing {rel}"
    return path.read_text(encoding="utf-8", errors="replace")


def test_scalar_vacuum_source_instantiates_cmp119_vacuum_as_scalar_by_type():
    text = read(
        "DASHI/Physics/Foundations/"
        "CMP119AntigravityScalarVacuumSourceActionExact.agda"
    )
    for token in (
        "scalarVacuumAssemble",
        "scalarVacuumAlgebra",
        "ScalarVacuumSourceInstantiation",
        "vacuumEnergyIsRationalByConstruction",
        "sourceEquation223UsesScalarVacuumAssembly",
        "scalarVacuumAssemblyEmbedsConstantAsIrrelevantAction",
        "allLocalizedActionVacuumAdapterPreferred",
        "postHocVacuumConstantEncodingReceiptRequiredOnPreferredRoute",
    ):
        assert token in text
