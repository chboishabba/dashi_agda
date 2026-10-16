#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "sources": ROOT / "DASHI/Biology/KitzerowBH4NeuralContextSourceAtlasExact.agda",
    "redox": ROOT / "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorExact.agda",
    "redox_v": ROOT / "DASHI/Biology/KitzerowBH4RedoxSpatialDiscriminatorValidation.agda",
    "experiment": ROOT / "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "pareto": ROOT / "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "status": ROOT / "DASHI/Chemistry/LineageEvidenceAcquisitionStatusExact.agda",
    "chem_v": ROOT / "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
    "domain_v": ROOT / "DASHI/Biology/KitzerowBH4MaxCutValidation.agda",
}
for key, path in paths.items():
    assert path.exists(), f"missing {key}: {path}"
text = {k: p.read_text() for k, p in paths.items()}

for needle in [
    "anastasiadisKuhnLevine1994Uptake", "choiEtAl2003HumanNnosUptake",
    "10.1016/0006-8993(94)91154-1", "10.1016/j.neulet.2003.08.032",
    "hwangEtAl1998Localization", "liangKaufman1998Striatum",
    "witteveenGiovanelliKaufman1999NOSRedox",
]:
    assert needle in text["sources"], f"source atlas missing {needle}"

for needle in [
    "cellularUptakeNode", "humanNnosRecipientNode", "exogenousBH4UptakeEdge",
    "catecholaminergicToNnosFunctionalCrossTalk", "monoamineToNnosTransferHypothesis",
    "cellularBH4UptakeDirectlyMeasured", "functionalCocultureCrossTalkSupported",
    "specificMembraneCarrierRequiredByUptakeStudy", "intercellBH4TransferDirectlyMeasured",
    "scalarWellMixedPoolSufficient", "redoxSpatialEvidenceClosesWholeAllocator",
]:
    assert needle in text["redox"], f"redox/spatial owner missing {needle}"

for needle in [
    "cellularUptakeAndFunctionalCrossTalkArePaidWithoutInventingFlux",
    "redoxRegenerationAndSpatialTopologyArePaidWithoutScalarPoolPromotion",
]:
    assert needle in text["redox_v"], f"redox validation missing {needle}"

for needle in [
    "historicalRedoxSpatialConstraintPaid", "quantitative donor-to-recipient BH4 transfer",
    "cellular uptake and functional coculture crosstalk are already paid",
    "historicalConstraintsCloseCentralEdge",
]:
    assert needle in text["experiment"], f"forward experiment missing {needle}"

for needle in [
    "target-relevant transfer/route-resolved multi-branch BH4 allocation experiment",
    "quantitative donor-to-recipient transfer", "uptake/coculture",
    "historicalDirectDiscriminatorClosesWholeTarget",
]:
    assert needle in text["pareto"], f"Pareto target missing {needle}"

for needle in [
    "bh4RedoxSpatialStatus", "direct cellular BH4 uptake",
    "functional catecholaminergic-to-nNOS coculture crosstalk",
    "quantitative donor-to-recipient transfer flux",
    "directIntercellularTransferAlreadyPaid",
]:
    assert needle in text["status"], f"status ledger missing {needle}"

for needle in [
    "bh4TransportEvidenceDoesNotRequireDedicatedCarrierOrQuantifyInVivoFlux",
    "bh4RedoxSpatialCoordinateIsPaidWithoutInventingTransfer",
]:
    assert needle in text["chem_v"], f"chemistry validation missing {needle}"

assert "uptakeAndCocultureArePaidWithoutQuantitativeTransferPromotion" in text["domain_v"]

print("BH4 redox/spatial/transport max-cut source contract: PASS")
