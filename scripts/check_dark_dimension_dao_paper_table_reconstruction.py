from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDAOPaperTableReconstructionExact.agda": [
        "module DASHI.Empirical.DarkDimensionDAOPaperTableReconstructionExact where",
        "PaperTableBestFit",
        "extendedAnalysisBestFit",
        '"0.02318"',
        '"0.1382"',
        '"72.50"',
        '"3.051"',
        '"0.9798"',
        '"0.0581"',
        '"0.87"',
        '"3.350"',
        '"0.039"',
        '"58.6"',
        '"0.036"',
        "zStopDirectlyPublished",
        "zStopReconstructedFromEquation13",
        "equation13ApproximationRetained",
        "originalMCMCManifestRecovered",
        "reconstructionManifestRunnable",
        "paperBestFitDoesNotEqualOriginalMCMCManifest",
        "approximateZStopDoesNotBecomeExactSampledCoordinate",
        "reconstructionCanRunWithoutClaimingOriginalCustody",
        "2602.23895",
    ],
    "scripts/reconstruct_dark_dimension_dao_paper_table_manifest.py": [
        "PAPER_ARXIV = \"2602.23895\"",
        "LOG10_ZDEC_BEST_FIT = 3.350",
        "G_OVER_AH_INI = 1.0e7",
        "z_stop = (1.0 + z_dec) * math.log(G_OVER_AH_INI) - 1.0",
        "A_s = math.exp(3.051) * 1.0e-10",
        "def render_class_ini",
        '"N_ur": 2.0308',
        '"N_ncdm": 1',
        '"m_ncdm": 0.06',
        '"T_ncdm": 0.716',
        '"YHe": "BBN"',
        '"manifest_kind": "paper-table-reconstruction"',
        '"original_mcmc_manifest_recovered": False',
        '"equation13_approximation_used": True',
        '"z_stop_directly_published": False',
        'choices=("json", "class-ini")',
    ],
    "DASHI/Empirical/DarkDimensionDAOParameterManifestBoundaryExact.agda": [
        "import DASHI.Empirical.DarkDimensionDAOPaperTableReconstructionExact as PaperReconstruction",
        "paperTableReconstructionDoesNotCloseOriginalManifestDebt",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_dao_paper_table_reconstruction.py",
        "python scripts/reconstruct_dark_dimension_dao_paper_table_manifest.py",
        "python scripts/reconstruct_dark_dimension_dao_paper_table_manifest.py --format class-ini",
        "DASHI/Empirical/DarkDimensionDAOPaperTableReconstructionExact.agda",
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

print("Dark-dimension DAO paper-table reconstruction static contract: OK")
