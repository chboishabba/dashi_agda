from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "matrix": root / "DASHI/Biology/Molecular/BH4PanelStoichiometricMatrixExact.agda",
    "parameters": root / "DASHI/Biology/BH4CompartmentKineticStateExact.agda",
    "nos": root / "DASHI/Biology/BH4NOSCouplingSameObjectExact.agda",
    "flux": root / "DASHI/Biology/BH4JointFluxFeasibilityExact.agda",
    "open_network": root / "DASHI/Biology/BH4OpenMetabolicNetworkAdapterExact.agda",
    "matrix_builder": root / "scripts/build_bh4_stoichiometric_matrix.py",
    "parameter_acquirer": root / "scripts/acquire_bh4_parameter_evidence.py",
    "flux_runner": root / "scripts/run_bh4_flux_feasibility.py",
    "regression": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
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
    "BH4NOSSameObjectPayment", "bh4Bh2StatePaid", "redoxStatePaid",
    "couplingTransitionPaid", "nitricOxideProductPaid",
    "nitrousOxideMayStandForNitricOxideProduct",
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
    "species_index", "reaction_index", "matrix", "finite_formula_residuals",
    "signed_coefficient",
]:
    assert token in text["matrix_builder"], f"missing matrix builder token: {token}"

for token in [
    "payment_status", "same_object_reference", "compartment_reference",
    "measurement_time_reference", "unresolved",
]:
    assert token in text["parameter_acquirer"], f"missing parameter acquirer token: {token}"

for token in [
    "feasible", "infeasible", "underdetermined", "missing_flux_bounds",
    "external_exchange", "candidate_flux_balance_witness",
]:
    assert token in text["flux_runner"], f"missing flux runner token: {token}"

print("BH4 phase-4 system-state max-cut regression: ok")
