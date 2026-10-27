from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

FINITE = ROOT / "DASHI/Quantum/QuantumBirthmarkFiniteRMTExact.agda"
SECTOR = ROOT / "DASHI/Quantum/QuantumBirthmarkSymmetrySectorExact.agda"
REVIVAL = ROOT / "DASHI/Quantum/QuantumBirthmarkRevivalExact.agda"
STADIUM = ROOT / "DASHI/Quantum/QuantumBirthmarkStadiumReceiptExact.agda"
ROLLUP = ROOT / "DASHI/Quantum/Everything.agda"


def test_finite_n_universal_factors_are_exactly_represented():
    text = FINITE.read_text()
    assert "gueFiniteFactor N = fraction (2 * N) (N + 1)" in text
    assert "goeFiniteFactor N = fraction (3 * N) (N + 2)" in text
    assert "largeNLimitWithoutTRS = 2" in text
    assert "largeNLimitWithTRS = 3" in text
    assert "arXiv:2602.00891" in text


def test_symmetry_sector_weighting_is_not_collapsed():
    text = SECTOR.read_text()
    assert "singleSectorRecoversStandardFactor" in text
    assert "uniformSectorSpanRecoversStandardFactor" in text
    assert "intermediateSectorWeightingMayExceedStandardFactor" in text
    assert "sectorStructureCannotBeDropped" in text


def test_revival_factor_is_short_time_correction_not_scar_synonym():
    text = REVIVAL.read_text()
    assert "revivalBeforeHeisenberg" in text
    assert "rmtBaseline" in text
    assert "revivalCorrectedBirthmark" in text
    assert "scarNotRequiredForRevival" in text
    assert "fullRevivalAfterHeisenbergIsDifferentRegime" in text


def test_stadium_numbers_are_example_receipts_only():
    text = STADIUM.read_text()
    assert "softA = decimalTenths 41" in text
    assert "softD = decimalHundredths 182" in text
    assert "hardA = decimalTenths 42" in text
    assert "hardD = decimalHundredths 198" in text
    assert "stadiumDoesNotProveUniversalFactor" in text


def test_round2_modules_are_registered():
    text = ROLLUP.read_text()
    for name in [
        "QuantumBirthmarkFiniteRMTExact",
        "QuantumBirthmarkSymmetrySectorExact",
        "QuantumBirthmarkRevivalExact",
        "QuantumBirthmarkStadiumReceiptExact",
    ]:
        assert f"DASHI.Quantum.{name}" in text
