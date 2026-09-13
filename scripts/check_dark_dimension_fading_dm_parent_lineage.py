from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

REQUIRED = {
    "DASHI/Empirical/DarkDimensionFadingDMParentLineageExact.agda": [
        "module DASHI.Empirical.DarkDimensionFadingDMParentLineageExact where",
        "Agrawal; Georges Obied; Cumrun Vafa",
        "H0 Tension, Swampland Conjectures and the Epoch of Fading Dark Matter",
        "10.1103/PhysRevD.103.043523",
        "1906.08261",
        "parentModelIdentified",
        "childReanalysisRelationshipLocated",
        "parentModifiedCLASSMontePythonLocated",
        "childCLASSCobayaLocated",
        "parentMassLawLocated",
        "parentPotentialLawLocated",
        "childLocalMassLawLocated",
        "childLocalPotentialLawLocated",
        "exactImplementationInheritanceDemonstrated",
        "normalizationInheritanceSameObject",
        "parentChainLocatedByCurrentSearch",
        "parentLineageDoesNotEqualImplementationIdentity",
        "parentNormalizationDoesNotAutoPayChildNormalization",
        "sameProposalFamilyDoesNotMeanSameNumericalManifest",
        "parentMassLawDiffersFromChildLocalMassLaw",
        "parentPotentialLawDiffersFromChildLocalPotentialLaw",
    ],
    "DASHI/Empirical/DarkDimensionBedroyaParameterManifestBoundaryExact.agda": [
        "import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage",
        "parentLineageStillDoesNotPayNormalizationMap",
        "parentImplementationInheritanceStillOpen",
    ],
    "DASHI/Empirical/DarkDimensionResidualDebtRoutingExact.agda": [
        "import DASHI.Empirical.DarkDimensionFadingDMParentLineageExact as ParentLineage",
        "parentLineageStillLeavesSameObjectGap",
    ],
    ".github/workflows/gr-quantum-empirical-validation.yml": [
        "python scripts/check_dark_dimension_fading_dm_parent_lineage.py",
        "DASHI/Empirical/DarkDimensionFadingDMParentLineageExact.agda",
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

print("Dark-dimension fading-DM parent lineage static contract: OK")
