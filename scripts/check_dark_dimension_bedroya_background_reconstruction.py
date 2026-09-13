from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionBedroyaBackgroundReconstructionExact.agda": [
        "module DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact where",
        "BedroyaBackgroundReconstructionStatus",
        "potentialEquationLocated",
        "darkMatterMassEquationLocated",
        "effectivePotentialEquationLocated",
        "friedmannEquationLocated",
        "kleinGordonEquationLocated",
        "desiBackgroundObservableEquationLocated",
        "pantheonNegativeCBestFitLocated",
        "standardCosmologyBestFitManifestLocated",
        "normalizationManifestLocated",
        "backgroundIntegratorExecutable",
        "sixKeyBAOVectorDerived",
        '"V = V0 exp(-c phi)"',
        '"m_DM = m0 exp(-cPrime phi)"',
        '"V_eff = V0 exp(-c phi) + m0 n0 a^-3 exp(-cPrime phi)"',
        '"phi_ddot + 3 H phi_dot + dV_eff/dphi = 0"',
        '"D_M(z) = integral_0^z dzPrime / H(zPrime)"',
        '"D_H(z) = 1 / H(z)"',
        '"-0.85"',
        '"0.05"',
        "equationsDoNotEqualNumericalManifest",
        "bestFitCouplingsDoNotDetermineBackgroundVector",
        "backgroundReconstructionStillOpen",
        "sixKeyVectorStillOpen",
        "2507.03090",
        "10.1103/1rsq-cv2m",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionBedroyaBackgroundReconstructionExact as BedroyaBackground",
        "darkDimensionBackgroundReconstructionStillOpen",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_bedroya_background_reconstruction.py",
        "DASHI/Empirical/DarkDimensionBedroyaBackgroundReconstructionExact.agda",
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

print("Dark-dimension Bedroya background reconstruction static contract: OK")
