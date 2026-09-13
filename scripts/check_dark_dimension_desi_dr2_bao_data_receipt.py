from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDESIDR2BAODataReceiptExact.agda": [
        "module DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact where",
        "SignedDecimalRatio",
        "AnisotropicBAOMeasurement",
        "lrg1Measurement",
        "lrg2Measurement",
        "lrg3Elg1Measurement",
        "elg2Measurement",
        "qsoMeasurement",
        "lyaMeasurement",
        "withinBinCorrelationRecorded",
        "fullCovarianceAssemblyStillOpen",
        "retrospectiveDataDoesNotPayHeldOutPrediction",
        "10.1103/tr6y-kpc6",
    ],
    "DASHI/Empirical/DarkDimensionSharedBAOProspectiveWeldExact.agda": [
        "import DASHI.Empirical.DarkDimensionDESIDR2BAODataReceiptExact as DR2Data",
        "retrospectiveDR2DataStillDoesNotLockProspectiveSeparation",
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
