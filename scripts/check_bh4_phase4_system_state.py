from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "matrix": root / "DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda",
    "parameters": root / "DASHI/Biology/BH4CompartmentKineticStateExact.agda",
    "nos_evidence": root / "DASHI/Biology/BH4NOSCouplingEvidenceExact.agda",
    "nos": root / "DASHI/Biology/BH4NOSCouplingSameObjectExact.agda",
    "flux": root / "DASHI/Biology/BH4JointFluxFeasibilityExact.agda",
    "open_network": root / "DASHI/Biology/BH4OpenMetabolicNetworkAdapterExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "matrix_builder": root / "scripts/build_bh4_stoichiometric_matrix.py",
    "parameter_acquirer": root / "scripts/acquire_bh4_parameter_evidence.py",
    "flux_runner": root / "scripts/run_bh4_flux_feasibility.py",
    "regression": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
    "external_root": root / "DASHI/Biology/ExternalBiologyEverything.agda",
    "kitzerow_root": root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda",
    "unified_root": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing phase-4 {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in [
    "BH4PanelStoichiometricMatrix", "signedCoefficient", "speciesIndex",
    "reactionIndex", "formulaIncompleteReactionBecomesZeroColumn",
]:
    assert token in text["matrix"], f"missing matrix token: {token}"

for token in [
    "ParameterPaymentStatus", "unresolvedParameter", "sameObjectReference",
    "compartmentReference", "measurementTimeReference",
    "unresolvedParameterMayBeReadAsMeasuredZero",
]:
    assert token in text["parameters"], f"missing parameter token: {token}"

for token in [
    "10.1074/jbc.M805403200", "10.1074/jbc.M109.041483",
    "bh4RelativeToNOS3", "bh4ToBh2RedoxRatio", "superoxideOutput",
    "nos3EvidenceGlobalizesToNOS1",
]:
    assert token in text["nos_evidence"], f"missing NOS3 evidence token: {token}"

for token in [
    "BH4NOSSameObjectPayment", "bh4Bh2StatePaid", "redoxStatePaid",
    "couplingTransitionPaid", "nitricOxideProductPaid",
    "nitrousOxideMayStandForNitricOxideProduct",
    "nos3RecyclingPerturbationLiteratureEvidence",
]:
    assert token in text["nos"], f"missing NOS token: {token}"

for token in [
    "FluxFeasibilityStatus", "underdetermined", "candidateFluxBalanceWitness",
    "missingFluxBoundMayBeSubstitutedWithZero", "feasibleFluxStateProvesDiseaseMechanism",
]:
    assert token in text["flux"], f"missing flux token: {token}"

for token in [
    "OpenMetabolicNetwork", "MetabolicOpenSystemBalance",
    "externalExchangeMayBeCollapsedIntoInternalStoichiometry",
]:
    assert token in text["open_network"], f"missing open-network token: {token}"

for token in [
    "currentBH4Phase", "systemStateQuantitativePhase", "wholeSystemFluxBalanceAttempted",
    "firstJointFluxOutcome", "underdetermined", "livePhase4Residuals",
]:
    assert token in text["roadmap"], f"missing roadmap token: {token}"

for token in [
    "species_index", "reaction_index", "matrix", "finite_formula_residuals",
    "signed_coefficient",
]:
    assert token in text["matrix_builder"], f"missing matrix builder token: {token}"

for token in [
    "payment_status", "same_object_reference", "compartment_reference",
    "measurement_time_reference", "unresolved", "REACTION_FLUX:",
]:
    assert token in text["parameter_acquirer"], f"missing parameter acquirer token: {token}"

for token in [
    "feasible", "infeasible", "underdetermined", "missing_flux_bounds",
    "external_exchange", "candidate_flux_balance_witness",
]:
    assert token in text["flux_runner"], f"missing flux runner token: {token}"

for root_name in ["external_root", "kitzerow_root", "unified_root"]:
    for token in [
        "BH4PanelStoichiometricMatrixExact", "BH4CompartmentKineticStateExact",
        "BH4NOSCouplingEvidenceExact", "BH4NOSCouplingSameObjectExact",
        "BH4JointFluxFeasibilityExact", "BH4OpenMetabolicNetworkAdapterExact",
        "BH4Phase4RoadmapExact", "BH4Phase4SystemStateRegression",
    ]:
        assert token in text[root_name], f"missing {root_name} phase-4 import: {token}"

print("BH4 phase-4 system-state max-cut regression: ok")
