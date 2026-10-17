from pathlib import Path

root = Path(__file__).resolve().parents[1]
files = {
    "evidence": root / "DASHI/Biology/BH4QuantitativeAcquisitionExact.agda",
    "sabio_receipt": root / "DASHI/Biology/BH4ExecutedSABIOReceiptExact.agda",
    "sabio_adjudication_receipt": root / "DASHI/Biology/BH4ExecutedSABIOAdjudicationReceiptExact.agda",
    "ranking_exact": root / "DASHI/Biology/BH4FluxCandidateRankingExact.agda",
    "payment_exact": root / "DASHI/Biology/BH4FluxPaymentPreparationExact.agda",
    "gap_evidence": root / "DASHI/Biology/BH4MissingReactionKineticsEvidenceExact.agda",
    "sifts_receipt": root / "DASHI/Biology/BH4ExecutedSIFTSReceiptExact.agda",
    "solver": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "rhea": root / "scripts/acquire_rhea_chebi_bh4_reactions.py",
    "sabio": root / "scripts/acquire_bh4_sabio_kinetics.py",
    "sabio_adjudication": root / "scripts/build_bh4_sabio_adjudication.py",
    "ranking": root / "scripts/rank_bh4_flux_candidates.py",
    "payment": root / "scripts/prepare_bh4_flux_payment.py",
    "sifts": root / "scripts/acquire_bh4_pdbe_sifts.py",
    "parameters": root / "scripts/acquire_bh4_parameter_evidence.py",
    "interval_solver": root / "scripts/solve_bh4_flux_intervals.py",
    "runner": root / "scripts/run_bh4_phase4_maxcut.py",
    "runbook": root / "docs/biology/BH4Phase4QuantitativeRunbook.md",
    "phase4_checker": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
    "unified": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}
for name, path in files.items(): assert path.exists(), f"missing quantitative max-cut {name}: {path.relative_to(root)}"
text = {name: path.read_text() for name, path in files.items()}

def require(name, tokens):
    for token in tokens: assert token in text[name], f"missing {name} token: {token}"

require("sabio_receipt", ["executedSABIOKineticEntryCount","executedSABIOKineticParameterCount","190","932","parameterObjectCreatesInVivoFluxBound"])
require("sabio_adjudication_receipt", ["executedMappedParameterCandidateCount","executedFiniteReactionCoverage","875","10","475","160","139","83","30","45","RHEA:11920","RHEA:19897"])
require("ranking_exact", ["FluxRelevanceClass","directRateCandidate","capacityCandidate","kineticShapeCandidate","missingPaymentGateDefaultsTrue"])
require("payment_exact", ["BH4FluxEvidenceClass","assaySpecificCapacity","turnoverCapacity","kineticShapeOnly","primaryLiteratureGap","specificActivityCreatesCompartmentFlux","kcatCreatesFluxWithoutAbundance"])
require("gap_evidence", ["RHEA:11920","RHEA:19897","PMID:9224737","PMID:9089781","primaryKineticsCreatesNetworkFluxBound"])
require("roadmap", ["executeFluxPaymentPreparation","payAssayReactionIdentityGates","paySameObjectCompartmentTimeGates","payNormalizedFluxUnitGates","payKineticToFluxTranslationGates","fluxPaymentPreparationToolReady = true","sabioKineticParameterCount","sabioFiniteReactionCandidateCoverage","sabioUnclassifiedParameterCandidates","expandedQuantitativeCoordinateCount = 56"])
require("rhea", ["NETWORK_ATTEMPTS = 3","NETWORK_BACKOFF_SECONDS","_retry","network_retry_exhaustion_means_reaction_absent"])
require("sabio", ["dashi.bh4-sabio-kinetics.v3","n_start_value","n_end_value","kinetic_parameter_candidates"])
require("sabio_adjudication", ["dashi.bh4-sabio-adjudication.v2","catalytic-constant-like","inhibitory-like","concentration-like","uncovered_finite_reactions"])
require("ranking", ["dashi.bh4-flux-candidate-ranking.v1","direct-rate-candidate","capacity-candidate","assay_reaction_identity_paid","usable_for_flux_bound"])
require("payment", ["dashi.bh4-flux-payment-preparation.v1","assay-specific-capacity","turnover-capacity","kinetic-shape-only","primary-literature-gap","enzyme_abundance_required","normalization_bridge_required","steady_state_flux_bound_payable"])
require("interval_solver", ["scipy.optimize","linprog","REACTION_FLUX:","EXCHANGE:","underdetermined"])
require("runner", ["rank_bh4_flux_candidates.py","prepare_bh4_flux_payment.py","bh4-flux-payment-preparation.json","dashi.bh4-phase4-maxcut-run.v6","sabio_flux_payment"])
require("unified", ["BH4ExecutedSABIOAdjudicationReceiptExact","BH4FluxCandidateRankingExact","BH4FluxPaymentPreparationExact","BH4MissingReactionKineticsEvidenceExact","BH4IntervalFluxSolverExact"])
print("BH4 Phase-4 quantitative acquisition + ranking + payment preparation + interval solver regression: ok")
