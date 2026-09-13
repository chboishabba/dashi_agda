from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionDAOSameKeyExtractionRecipeExact.agda": [
        "module DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact where",
        "DAOSameKeyExtractionRecipe",
        "daoPinnedExtractionRecipe",
        "input/DRMD.ini",
        "python/classy.pyx",
        "angular_distance",
        "Hubble",
        "rs_drag",
        "rs_d_drmd",
        "transverseDistanceFormula",
        "radialDistanceFormula",
        "darkSoundHorizonDoesNotSubstituteForBAODragHorizon",
        "lrg1TransverseExtractionRequest",
        "lrg1RadialExtractionRequest",
        "recipeExecuted",
        "recipeExecutionStillOpen",
        "sameKeyBAOVectorStillNotDerived",
        "aa2b61a0f1cf246672cdbd4634a4797d4cc654f9",
    ],
    "DASHI/Empirical/DarkDimensionSameKeyPredictionDebtExact.agda": [
        "import DASHI.Empirical.DarkDimensionDAOSameKeyExtractionRecipeExact as DAORecipe",
        "daoExtractionRecipeLocatedButExecutionStillOpen",
        "input/DRMD.ini",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_dao_same_key_extraction_recipe.py",
        "DASHI/Empirical/DarkDimensionDAOSameKeyExtractionRecipeExact.agda",
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

print("Dark-dimension DAO same-key extraction recipe static contract: OK")
