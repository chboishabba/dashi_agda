from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "executed": root / "DASHI/Biology/Molecular/BH4ExecutedPanelReactionReceiptExact.agda",
    "matrix": root / "DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda",
    "parameters": root / "DASHI/Biology/BH4CompartmentKineticStateExact.agda",
    "quantitative": root / "DASHI/Biology/BH4QuantitativeAcquisitionExact.agda",
    "sabio_receipt": root / "DASHI/Biology/BH4ExecutedSABIOReceiptExact.agda",
    "sabio_adjudication_receipt": root / "DASHI/Biology/BH4ExecutedSABIOAdjudicationReceiptExact.agda",
    "ranking_exact": root / "DASHI/Biology/BH4FluxCandidateRankingExact.agda",
    "gap_evidence": root / "DASHI/Biology/BH4MissingReactionKineticsEvidenceExact.agda",
    "sifts_receipt": root / "DASHI/Biology/BH4ExecutedSIFTSReceiptExact.agda",
    "interval": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "nos_evidence": root / "DASHI/Biology/BH4NOSCouplingEvidenceExact.agda",
    "nos": root / "DASHI/Biology/BH4NOSCouplingSameObjectExact.agda",
    "flux": root / "DASHI/Biology/BH4JointFluxFeasibilityExact.agda",
    "open_network": root / "DASHI/Biology/BH4OpenMetabolicNetworkAdapterExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "matrix_builder": root / "scripts/build_bh4_stoichiometric_matrix.py",
    "parameter_acquirer": root / "scripts/acquire_bh4_parameter_evidence.py",
    "sabio": root / "scripts/acquire_bh4_sabio_kinetics.py",
    "sabio_adjudication": root / "scripts/build_bh4_sabio_adjudication.py",
    "ranking": root / "scripts/rank_bh4_flux_candidates.py",
    "sifts": root / "scripts/acquire_bh4_pdbe_sifts.py",
    "interval_solver": root / "scripts/solve_bh4_flux_intervals.py",
    "flux_runner": root / "scripts/run_bh4_flux_feasibility.py",
    "regression": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
    "external_root": root / "DASHI/Biology/ExternalBiologyEverything.agda",
    "kitzerow_root": root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda",
    "unified_root": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing phase-4 {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in ["proteinReactionLinkCount", "finiteReactionCount", "residualReactionCount", "finiteSpeciesCount", "24 12 3 29", "RHEA:17473", "RHEA:19897", "RHEA:36255"]:
    assert token in text["executed"], f"missing executed-panel token: {token}"

for token in ["executedPanelSpeciesCount", "executedPanelReactionCount", "formulaIncompleteReactionBecomesZeroColumn"]:
    assert token in text["matrix"], f"missing matrix token: {token}"

for token in ["unresolvedParameter", "sameObjectReference", "compartmentReference", "measurementTimeReference", "unresolvedParameterMayBeReadAsMeasuredZero"]:
    assert token in text["parameters"], f"missing parameter token: {token}"

for token in ["kineticConstantCreatesFluxBound", "structureMappingCreatesCatalyticMechanism"]:
    assert token in text["quantitative"], f"missing quantitative acquisition token: {token}"

for token in ["executedSABIOKineticEntryCount", "executedSABIOKineticParameterCount", "190", "932", "parameterObjectCreatesInVivoFluxBound"]:
    assert token in text["sabio_receipt"], f"missing SABIO receipt token: {token}"

for token in ["executedMappedParameterCandidateCount", "executedFiniteReactionCoverage", "executedUnclassifiedCount", "875", "10", "45", "parameterKindCreatesFluxPayment"]:
    assert token in text["sabio_adjudication_receipt"], f"missing SABIO adjudication receipt token: {token}"

for token in ["FluxRelevanceClass", "rankCreatesFluxBound", "catalyticConstantCreatesFluxWithoutEnzymeAbundance", "missingPaymentGateDefaultsTrue"]:
    assert token in text["ranking_exact"], f"missing ranking exact token: {token}"

for token in ["PCBD1", "NOS", "RHEA:11920", "RHEA:19897", "primaryKineticsCreatesNetworkFluxBound"]:
    assert token in text["gap_evidence"], f"missing gap evidence token: {token}"

for token in ["executedStructuresExamined", "38", "executedMatchingSIFTSSegmentCount", "526", "mappingCreatesCatalyticFunction"]:
    assert token in text["sifts_receipt"], f"missing SIFTS receipt token: {token}"

for token in ["IntervalFluxSolverStatus", "underdetermined", "missingExchangeBoundMayBeSubstitutedWithZero"]:
    assert token in text["interval"], f"missing interval solver token: {token}"

for token in ["10.1074/jbc.M805403200", "10.1074/jbc.M109.041483", "nos3EvidenceGlobalizesToNOS1"]:
    assert token in text["nos_evidence"], f"missing NOS3 evidence token: {token}"

for token in ["BH4NOSSameObjectPayment", "couplingTransitionPaid", "nitrousOxideMayStandForNitricOxideProduct"]:
    assert token in text["nos"], f"missing NOS token: {token}"

for token in ["missingFluxBoundMayBeSubstitutedWithZero", "feasibleFluxStateProvesDiseaseMechanism"]:
    assert token in text["flux"], f"missing flux token: {token}"

for token in ["OpenMetabolicNetwork", "MetabolicOpenSystemBalance", "externalExchangeMayBeCollapsedIntoInternalStoichiometry"]:
    assert token in text["open_network"], f"missing open-network token: {token}"

for token in ["currentBH4Phase", "systemStateQuantitativePhase", "rankSABIOCandidatesByFluxRelevance", "translatePCBD1NOSPrimaryKineticsIntoReactionBounds", "fluxCandidateRankingToolReady", "sabioKineticParameterCount", "sabioMappedParameterCandidates", "sabioFiniteReactionCandidateCoverage", "sabioUnclassifiedParameterCandidates", "missingReactionFluxBounds = 12", "missingExternalExchangeCoordinates = 29"]:
    assert token in text["roadmap"], f"missing roadmap token: {token}"

for token in ["species_index", "reaction_index", "matrix", "finite_formula_residuals", "signed_coefficient"]:
    assert token in text["matrix_builder"], f"missing matrix builder token: {token}"

for token in ["payment_status", "same_object_reference", "compartment_reference", "measurement_time_reference", "REACTION_FLUX:", "EXCHANGE:"]:
    assert token in text["parameter_acquirer"], f"missing parameter acquirer token: {token}"

for token in ["UniProtKB_AC", "n_start_value", "kinetic_parameter_candidates", "kinetic_parameters_create_flux_bounds"]:
    assert token in text["sabio"], f"missing SABIO acquisition token: {token}"

for token in ["finite_matrix_rhea_ids", "usable_for_flux_bound", "parameter_kind_hint", "uncovered_finite_reactions"]:
    assert token in text["sabio_adjudication"], f"missing SABIO adjudication token: {token}"

for token in ["direct-rate-candidate", "capacity-candidate", "usable_for_flux_bound", "blocked_by", "top_candidates_by_reaction"]:
    assert token in text["ranking"], f"missing ranking script token: {token}"

for token in ["_pdbx_sifts_unp_segments", "structure_mapping_creates_catalytic_mechanism"]:
    assert token in text["sifts"], f"missing SIFTS acquisition token: {token}"

for token in ["scipy.optimize", "linprog", "REACTION_FLUX:", "EXCHANGE:", "solver-unavailable"]:
    assert token in text["interval_solver"], f"missing interval-solver script token: {token}"

for root_name in ["external_root", "kitzerow_root", "unified_root"]:
    for token in ["BH4ExecutedSABIOAdjudicationReceiptExact", "BH4FluxCandidateRankingExact", "BH4MissingReactionKineticsEvidenceExact", "BH4Phase4SystemStateRegression"]:
        assert token in text[root_name], f"missing {root_name} phase-4 import: {token}"

print("BH4 phase-4 system-state + ranked kinetic adjudication regression: ok")
