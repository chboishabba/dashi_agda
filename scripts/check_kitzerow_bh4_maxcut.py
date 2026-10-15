#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

required = [
    "DASHI/Biology/KitzerowBH4CascadeExact.agda",
    "DASHI/Biology/KitzerowBH4RepoIntegrationExact.agda",
    "DASHI/Biology/KitzerowBH4ReactionChemistryExact.agda",
    "DASHI/Biology/KitzerowBH4SynthesisRegenerationExact.agda",
    "DASHI/Biology/KitzerowBH4ReactionSourceAtlasExact.agda",
    "DASHI/Biology/KitzerowBH4ReactionCascadeBridgeExact.agda",
    "DASHI/Biology/KitzerowBH4SourceAtlasExact.agda",
    "DASHI/Biology/KitzerowBH4ConvergentEvidenceExact.agda",
    "DASHI/Biology/KitzerowPriorityAttributionExact.agda",
    "DASHI/Biology/KitzerowBH4PriorArtSubtractionExact.agda",
    "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "DASHI/Biology/KitzerowBH4Everything.agda",
    "DASHI/Biology/KitzerowBH4EverythingFull.agda",
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

reaction = (ROOT / "DASHI/Biology/KitzerowBH4ReactionChemistryExact.agda").read_text()
for needle in [
    "AtomicPeriodicTable369ChemistryHyperfibreBridgeExact",
    "gch1Reaction",
    "pahReaction",
    "thReaction",
    "tphReaction",
    "nosCoupledReaction",
    "nosUncoupledReaction",
    "agmoReaction",
    "speciesAndStoichiometryExplicit",
]:
    assert needle in reaction, f"literal reaction chemistry missing {needle}"

cycle = (ROOT / "DASHI/Biology/KitzerowBH4SynthesisRegenerationExact.agda").read_text()
for needle in ["ptpsReaction", "sprReaction", "pcdReaction", "dhprReaction", "fluxCompetitionQuantified"]:
    assert needle in cycle, f"BH4 synthesis/regeneration missing {needle}"

bridge = (ROOT / "DASHI/Biology/KitzerowBH4ReactionCascadeBridgeExact.agda").read_text()
for needle in ["aaaHReactionBranch", "nosReactionBranch", "agmoReactionBranch", "bh4SupplyRecycleBranch"]:
    assert needle in bridge, f"cascade/reaction bridge missing {needle}"

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

full = (ROOT / "DASHI/Biology/KitzerowBH4EverythingFull.agda").read_text()
assert "import DASHI.Biology.Everything" in full
assert "import DASHI.Biology.KitzerowBH4Everything" in full

print("kitzerow-bh4 reaction-aware max-cut static contract: PASS")
