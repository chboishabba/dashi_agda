#!/usr/bin/env python3
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]

paths = {
    "probe": "DASHI/Biology/KitzerowBH4NeuralInVivoRouteStateProbeExact.agda",
    "probe_v": "DASHI/Biology/KitzerowBH4NeuralInVivoRouteStateProbeValidation.agda",
    "status": "DASHI/Biology/KitzerowBH4NeuralRouteStateAcquisitionStatusExact.agda",
    "experiment": "DASHI/Biology/KitzerowBH4ExperimentalDiscriminatorExact.agda",
    "pareto": "DASHI/Biology/KitzerowBH4ParetoAcquisitionExact.agda",
    "bio_validation": "DASHI/Biology/KitzerowBH4MaxCutValidation.agda",
    "bio_rollup": "DASHI/Biology/KitzerowBH4Everything.agda",
    "chem_validation": "DASHI/Chemistry/LineageCalibrationDiscriminatorMaxCutValidation.agda",
    "chem_rollup": "DASHI/Chemistry/LineageCalibrationDiscriminatorEverything.agda",
}

for key, rel in paths.items():
    p = ROOT / rel
    assert p.exists(), f"missing {key}: {rel}"

text = {k: (ROOT / p).read_text() for k, p in paths.items()}

for needle in [
    "nakaharaEtAl1988Microdialysis",
    "koshimuraMiwaWatanabe1994Sepiapterin",
    "nagatsuEtAl1994TH",
    "ishidaEtAl1998TPH",
    "10.1016/0197-0186(88)90118-0",
    "10.1046/j.1471-4159.1994.63020649.x",
    "10.1016/0304-3940(94)90201-1",
    "10.1016/S0304-3940(98)00601-6",
    "totalTissueBiopterinSufficesForMonoamineOutput",
    "intracellularAndExtracellularBH4AreMechanisticallyEquivalent",
    "peripheralBH4CanActivateTHInVivo",
    "peripheralBH4CanActivateTPHInVivo",
    "sameObjectSimultaneousMultiBranchAllocationPaid",
    "canonicalRouteStateBackprop",
]:
    assert needle in text["probe"], f"route-state probe missing {needle}"

for needle in [
    "routeAndStateMatterBeyondTotalPoolAmount",
    "inVivoTHAndTPHResponsesArePaidButNotSimultaneousAllocation",
    "routeStateEvidenceDoesNotCloseWholeAllocator",
]:
    assert needle in text["probe_v"], f"route-state validation missing {needle}"

for needle in [
    "routeStateCoordinatePaid",
    "simultaneousAllocationCoordinatePaid",
    "wholeAllocatorClosed",
]:
    assert needle in text["status"], f"route-state status missing {needle}"

for needle in [
    "historicalRouteStateConstraint",
    "historicalRouteStateConstraintPaid",
    "donor-labelled BH4/BH2 transfer",
    "simultaneous TH/TPH/NOS/AGMO",
]:
    assert needle in text["experiment"], f"experiment backprop missing {needle}"

assert "target neural donor-labelled BH4/BH2 transfer with simultaneous multi-branch mediation" in text["pareto"]

for needle in [
    "routeStateEvidenceRejectsTotalPoolAndGenericExposureSufficiency",
    "routeStateAcquisitionIsPaidWithoutWholeClosure",
    "historicalRouteStateConstraintPaid",
]:
    assert needle in text["bio_validation"], f"biology validation missing {needle}"

for needle in [
    "bh4RouteStateEvidenceSeparatesPoolAmountFromBranchResponse",
    "bh4RouteStateStatusKeepsAllocatorOpen",
]:
    assert needle in text["chem_validation"], f"chemistry validation missing {needle}"

for needle in [
    "KitzerowBH4NeuralInVivoRouteStateProbeExact",
    "KitzerowBH4NeuralInVivoRouteStateProbeValidation",
    "KitzerowBH4NeuralRouteStateAcquisitionStatusExact",
]:
    assert needle in text["bio_rollup"], f"biology rollup missing {needle}"
    assert needle in text["chem_rollup"], f"chemistry rollup missing {needle}"

print("BH4 neural route/state max-cut static contract: PASS")
