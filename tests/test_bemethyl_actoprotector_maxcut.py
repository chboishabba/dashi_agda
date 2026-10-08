from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Biology/BemethylActoprotectorClaimAtlasExact.agda": [
        "module DASHI.Biology.BemethylActoprotectorClaimAtlasExact where",
        "mechanismResolved = false",
        "purineSimilarityProvesDNABinding = false",
        "historicalUseProvesEfficacy = false",
    ],
    "DASHI/Biology/BemethylMetabolicMechanismBoundaryExact.agda": [
        "module DASHI.Biology.BemethylMetabolicMechanismBoundaryExact where",
        "CoriCycleRoute",
        "MitochondrialEnzymeRoute",
        "AntioxidantEnzymeRoute",
        "proteinSynthesisDependenceDoesNotIdentifyTarget = refl",
    ],
    "DASHI/Biology/BemethylBioenergeticCrossPollinationExact.agda": [
        "module DASHI.Biology.BemethylBioenergeticCrossPollinationExact where",
        "existingATPAdapter",
        "sameObjectHumanValidationPaid = false",
        "mechanismHypothesisDoesNotUpgradeExistingATPTheorem = refl",
    ],
    "DASHI/Biology/BemethylActoprotectorMaxCutExact.agda": [
        "module DASHI.Biology.BemethylActoprotectorMaxCutExact where",
        "transcriptFormalised = true",
        "modernMechanismTargetIdentified = false",
        "modernHumanPerformanceReplicationPaid = false",
        "clinicalRecommendationPaid = false",
    ],
}

for rel, markers in REQUIRED.items():
    text = (ROOT / rel).read_text()
    for marker in markers:
        assert marker in text, (rel, marker)

rollup = (ROOT / "DASHI/Biology/BemethylActoprotectorEverything.agda").read_text()
for owner in REQUIRED:
    module = owner.removesuffix(".agda").replace("/", ".")
    assert f"import {module}" in rollup
