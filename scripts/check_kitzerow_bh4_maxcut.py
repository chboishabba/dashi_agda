#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = [
    "DASHI/Biology/KitzerowBH4CascadeExact.agda",
    "DASHI/Biology/KitzerowBH4RepoIntegrationExact.agda",
    "DASHI/Biology/KitzerowBH4SourceAtlasExact.agda",
    "DASHI/Biology/KitzerowBH4ConvergentEvidenceExact.agda",
    "DASHI/Biology/KitzerowPriorityAttributionExact.agda",
    "DASHI/Biology/KitzerowBH4PriorArtSubtractionExact.agda",
    "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "DASHI/Biology/KitzerowBH4Everything.agda",
    "DASHI/Biology/KitzerowBH4MaxCutValidation.agda",
]
for rel in required:
    assert (ROOT / rel).exists(), f"missing {rel}"

integration = (ROOT / "DASHI/Biology/KitzerowBH4RepoIntegrationExact.agda").read_text()
for needle in [
    "AllostaticBodyStateExact",
    "Cell.CellStateAttractor",
    "NeurochemicalBrainCarrierBridge",
    "GenomeSensorimotorConnectomeBridge",
    "NeurochemicalGenomicExpressionBridge",
    "PhysicsChemistryBiologyDNAUnificationDischarge",
    "ChemistryBiologyObligations",
    "NeurochemicalAuthorityBoundary",
]:
    assert needle in integration, f"integration missing {needle}"

attribution = (ROOT / "DASHI/Biology/KitzerowPriorityAttributionExact.agda").read_text()
for needle in [
    "originatorReportedContact",
    "independentDerivationSupported",
    "contactDoesNotProveUse",
    "citationAbsenceDoesNotProvePlagiarism",
]:
    assert needle in attribution, f"attribution firewall missing {needle}"

evidence = (ROOT / "DASHI/Biology/KitzerowBH4ConvergentEvidenceExact.agda").read_text()
assert "wholeModelConfirmed" in evidence
assert "allCanonicalEvidenceReceiptsRejectWholeModelConfirmation" in evidence

rollup = (ROOT / "DASHI/Biology/Everything.agda").read_text()
assert "import DASHI.Biology.KitzerowBH4Everything" in rollup

print("kitzerow-bh4 max-cut static contract: PASS")
