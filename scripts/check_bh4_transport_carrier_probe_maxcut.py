#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
paths = {
    "probe": "DASHI/Biology/KitzerowBH4TransportCarrierProbeExact.agda",
    "probe_v": "DASHI/Biology/KitzerowBH4TransportCarrierProbeValidation.agda",
    "status": "DASHI/Biology/KitzerowBH4TransportAcquisitionStatusExact.agda",
    "experiment": "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "pareto": "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "kit_rollup": "DASHI/Biology/KitzerowBH4Everything.agda",
    "chem_rollup": "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
    "chem_validation": "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
    "frontier": "DASHI/Chemistry/LineageAttributionAcquisitionFrontierExact.agda",
}
for key, rel in paths.items():
    assert (ROOT / rel).exists(), f"missing {key}: {rel}"
text = {k: (ROOT / p).read_text() for k, p in paths.items()}

for needle in [
    "choiJangKimHwang2000Release", "ohashiEtAl2009CacoTransport",
    "ohashiEtAl2011ENT", "ohashiEtAl2017OAT",
    "about 150 pmol/h per well", "specificTransportersExistInSomeContexts",
    "singleUniversalNeuralBH4CarrierEstablished",
    "neuralPassiveDiffusionResultUniversalizesToAllTissues",
    "transporterDependenceIsTissueSpeciesSubstrateSpecific",
    "quantitativeTranscellularBH4RatePaid", "quantitativeNeuralDonorRecipientFluxPaid",
    "catecholaminergicBH4ReleaseObserved", "recipientBH4UptakeObserved",
    "functionalCocultureCrossTalkObserved", "releaseUptakeCocultureSufficesForQuantitativeTransfer",
    "transportProbeClosesWholeAllocator", "canonicalTransportTopologyUpgrade",
]:
    assert needle in text["probe"], f"transport probe missing {needle}"

for needle in [
    "carrierQuestionIsContextSpecificNotUniversallyNegative",
    "quantitativeTranscellularTransportIsPaidWithoutNeuralFluxPromotion",
    "releaseUptakeAndCocultureDoNotBecomeMolecularTransferRate",
    "transportEvidenceDoesNotCloseAllocator",
]:
    assert needle in text["probe_v"], f"transport validation missing {needle}"

for needle in [
    "transportExistencePaid", "contextSpecificCarrierMechanismsPaid",
    "nonNeuralTranscellularRatePaid", "neuralDonorRecipientRatePaid",
    "wholeAllocatorClosed",
]:
    assert needle in text["status"], f"transport status missing {needle}"

for needle in [
    "historicalTransportCarrierConstraint", "historicalTransportCarrierConstraintPaid",
    "isotope-resolved donor-to-recipient", "transporter expression/inhibition",
]:
    assert needle in text["experiment"], f"experimental backprop missing {needle}"

for needle in [
    "target neural isotope-resolved donor-recipient BH4/BH2 transfer",
    "universal passive diffusion", "one universal dedicated carrier",
]:
    assert needle in text["pareto"], f"pareto frontier missing {needle}"

for relkey in ["kit_rollup", "chem_rollup"]:
    for needle in [
        "KitzerowBH4TransportCarrierProbeExact",
        "KitzerowBH4TransportCarrierProbeValidation",
        "KitzerowBH4TransportAcquisitionStatusExact",
    ]:
        assert needle in text[relkey], f"{relkey} missing {needle}"

for needle in [
    "bh4CarrierMechanismIsContextSpecific",
    "bh4QuantitativeTransportPaymentStopsBeforeTargetNeuralTransfer",
]:
    assert needle in text["chem_validation"], f"chem validation missing {needle}"

for needle in [
    "A1 target-neural isotope-resolved donor-recipient BH4/BH2 transfer",
    "transporter expression/inhibition", "donor-derived BH4/BH2 transfer rate/direction",
]:
    assert needle in text["frontier"], f"global frontier missing {needle}"

print("BH4 transport/carrier/intercellular-transfer max-cut static contract: PASS")
