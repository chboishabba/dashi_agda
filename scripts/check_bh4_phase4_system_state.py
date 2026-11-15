from pathlib import Path

root = Path(__file__).resolve().parents[1]
files = {
    "executed": root / "DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda",
    "matrix": root / "DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda",
    "parameters": root / "DASHI/Biology/BH4CompartmentKineticStateExact.agda",
    "sabio_receipt": root / "DASHI/Biology/BH4ExecutedSABIOReceiptExact.agda",
    "sabio_adjudication_receipt": root / "DASHI/Biology/BH4ExecutedSABIOAdjudicationReceiptExact.agda",
    "ranking_exact": root / "DASHI/Biology/BH4FluxCandidateRankingExact.agda",
    "payment_exact": root / "DASHI/Biology/BH4FluxPaymentPreparationExact.agda",
    "payment_regression": root / "DASHI/Biology/BH4FluxPaymentPreparationRegression.agda",
    "gap_evidence": root / "DASHI/Biology/BH4MissingReactionKineticsEvidenceExact.agda",
    "sifts_receipt": root / "DASHI/Biology/BH4ExecutedSIFTSReceiptExact.agda",
    "interval": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "regression": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
    "external_root": root / "DASHI/Biology/ExternalBiologyEverything.agda",
    "kitzerow_root": root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda",
    "unified_root": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}
for name, path in files.items(): assert path.exists(), f"missing phase-4 {name}: {path.relative_to(root)}"
text={name:path.read_text() for name,path in files.items()}
def req(name,tokens):
    for token in tokens: assert token in text[name], f"missing {name} token: {token}"
req("executed",["proteinReactionLinkCount","finiteReactionCount","residualReactionCount","finiteSpeciesCount","24 12 3 29"])
req("matrix",["executedPanelSpeciesCount","executedPanelReactionCount","formulaIncompleteReactionBecomesZeroColumn"])
req("parameters",["unresolvedParameterMayBeReadAsMeasuredZero","sameObjectReference","compartmentReference","measurementTimeReference"])
req("sabio_receipt",["executedSABIOKineticParameterCount","932","parameterObjectCreatesInVivoFluxBound"])
req("sabio_adjudication_receipt",["executedMappedParameterCandidateCount","executedFiniteReactionCoverage","executedUnclassifiedCount","875","10","45","parameterKindCreatesFluxPayment"])
req("ranking_exact",["FluxRelevanceClass","rankCreatesFluxBound","catalyticConstantCreatesFluxWithoutEnzymeAbundance"])
req("payment_exact",["BH4FluxEvidenceClass","specificActivityCreatesCompartmentFlux","kcatCreatesFluxWithoutAbundance","shapeParameterCreatesMagnitudeBound"])
req("payment_regression",["specificActivityIsNotCompartmentFlux","kcatNeedsEnzymeAbundance","kineticShapeDoesNotPayMagnitude","paymentPreparationToolIsReady"])
req("gap_evidence",["RHEA:11920","RHEA:19897","primaryKineticsCreatesNetworkFluxBound"])
req("sifts_receipt",["executedStructuresExamined","38","executedMatchingSIFTSSegmentCount","526"])
req("interval",["underdetermined","missingExchangeBoundMayBeSubstitutedWithZero"])
req("roadmap",["currentBH4Phase","systemStateQuantitativePhase","executeFluxPaymentPreparation","payAssayReactionIdentityGates","paySameObjectCompartmentTimeGates","payNormalizedFluxUnitGates","payKineticToFluxTranslationGates","fluxCandidateRankingToolReady","fluxPaymentPreparationToolReady","sabioKineticParameterCount","sabioMappedParameterCandidates","sabioFiniteReactionCandidateCoverage","sabioUnclassifiedParameterCandidates","missingReactionFluxBounds = 12","missingExternalExchangeCoordinates = 29"])
for root_name in ["external_root","kitzerow_root","unified_root"]:
    req(root_name,["BH4ExecutedSABIOAdjudicationReceiptExact","BH4FluxCandidateRankingExact","BH4FluxPaymentPreparationExact","BH4FluxPaymentPreparationRegression","BH4MissingReactionKineticsEvidenceExact"])
print("BH4 phase-4 system-state + ranked kinetics + flux-payment preparation regression: ok")
