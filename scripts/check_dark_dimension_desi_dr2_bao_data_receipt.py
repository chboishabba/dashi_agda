from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDESIDR2BAODataReceiptExact.agda": [
        "module DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact where",
        "SignedDecimalRatio",
        "AnisotropicBAOMeasurement",
        "lrg1Measurement = mkMeasurement ObservationKey.lrg1 13588 167 21863 425 459",
        "lrg2Measurement = mkMeasurement ObservationKey.lrg2 17351 177 19455 330 404",
        "mkMeasurement ObservationKey.lrg3Elg1 21576 152 17641 193 416",
        "elg2Measurement = mkMeasurement ObservationKey.elg2 27601 318 14176 221 434",
        "qsoMeasurement = mkMeasurement ObservationKey.qso 30512 760 12817 516 500",
        "lyaMeasurement = mkMeasurement ObservationKey.lya 38988 531 8632 101 431",
        "withinBinCorrelationCoefficientRecorded",
        "withinBinCorrelationRecorded",
        "fullCovarianceAssemblyStillOpen",
        "retrospectiveDataDoesNotPayHeldOutPrediction",
        "10.1103/tr6y-kpc6",
    ],
    "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda": [
        "import DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact as DR2Data",
        "retrospectiveDR2DataStatusStillOpenForProspectiveSeparation",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_desi_dr2_bao_data_receipt.py",
        "DASHI/Empirical/DarkDimensionDESIDR2BAODataReceiptExact.agda",
    ],
}

missing = []
for rel, needles in REQUIRED.items():
    path = ROOT / rel
    if not path.exists():
        missing.append(f"missing file: {rel}")
        continue
    text = path.read_text(encoding="utf-8")
    for needle in needles:
        if needle not in text:
            missing.append(f"{rel}: missing {needle}")

if missing:
    raise SystemExit("\n".join(missing))

print("Dark-dimension DESI DR2 BAO data receipt static contract: OK")
