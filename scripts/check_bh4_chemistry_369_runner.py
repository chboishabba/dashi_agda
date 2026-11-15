from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "reaction": root / "DASHI/Biology/Molecular/BH4RheaChEBIReactionExact.agda",
    "stoich": root / "DASHI/Biology/Molecular/BH4MolecularStoichiometryExact.agda",
    "refinement": root / "DASHI/Interop/BH4Atomic369RefinementExact.agda",
    "runner_receipt": root / "DASHI/Biology/BH4ReactionNetworkRunnerReceipt.agda",
    "runner": root / "scripts/run_bh4_reaction_network.py",
    "rhea_acquirer": root / "scripts/acquire_rhea_chebi_bh4_reactions.py",
    "unified": root / "DASHI/Unified/BH4BiochemicalCrossScaleAdapter.agda",
    "focused": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
    "biology_root": root / "DASHI/Biology/ExternalBiologyEverything.agda",
    "kitzerow_root": root / "DASHI/Biology/KitzerowBH4EvidenceEverything.agda",
    "regression": root / "DASHI/Biology/BH4Chemistry369RunnerRegression.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in [
    "RHEA:17869", "RHEA:17871", "RHEA:32253",
    "CHEBI:43120", "CHEBI:59560", "CHEBI:15372", "CHEBI:57540",
    "CHEBI:57945", "CHEBI:15378", "reactionIdentityCreatesBiologicalMechanism",
]:
    assert token in text["reaction"], f"missing reaction token: {token}"

for token in [
    "qdprAtomAndChargeBalanced", "qdprAtomsConserved", "qdprChargeConserved",
    "balancedReactionCreatesKineticLaw", "balancedReactionCreatesDiseaseMechanism",
    "MolecularStoichiometricConservation",
]:
    assert token in text["stoich"], f"missing stoichiometry token: {token}"

for token in [
    "AtomicGenerationPipelineExact", "ArgumentLevelTransportHyperformalismExact",
    "PNFHyperfabric369", "NonginNangNitrogenOxideRefinementExact",
    "atomicInventorySolvesMolecularHamiltonian",
    "coarseBH4AvailabilityReconstructsFineChemicalState",
    "coarseNitrogenOxideCannotServeFineChemicalConsumer", "chemistryIsLiterally369",
]:
    assert token in text["refinement"], f"missing refinement token: {token}"

for token in [
    "stoichiometricRunnerCreatesMeasuredFlux", "runnerStateCreatesDiseaseMechanism",
    "BH4SystemState", "reactionIdentityPaid", "wholeSystemFluxMeasured",
]:
    assert token in text["runner_receipt"], f"missing runner receipt token: {token}"

for token in [
    "rhea_id", "stoichiometrically_balanced", "kinetics_supplied",
    "measured_flux_promoted", "disease_mechanism_promoted", "residuals",
    "--certificate", "audit_certificate", "formula_charge_audited",
    "finite_formula_residuals", "write_outputs", ".json", ".csv", ".md",
]:
    assert token in text["runner"], f"missing runner token: {token}"

for token in [
    "--from-uniprot-panel", "extract_panel_rhea", "complete_reaction_identity_acquisition",
    "RHEA_SPARQL", "fetch_rhea_participants", "rh:substrates", "rh:products",
    "rh:coefficient", "rh:formula", "rh:charge", "formula_charge_ready",
    "formula_charge_ready_reactions", "participant_sparql_response_sha256",
    "raw_sha256", "specific_chebi_fixture_paid", "reaction_identity_creates_kinetics",
]:
    assert token in text["rhea_acquirer"], f"missing Rhea acquirer token: {token}"

for token in [
    "CrossScaleMatterPhysics", "PhysicsChemistryBiologyDNAUnificationDischarge",
    "adapterCreatesFirstPrinciplesAtomsToCellsDerivation", "adapterCreatesDiseaseCausation",
    "cellularStatePredictionPaid",
]:
    assert token in text["unified"], f"missing unified adapter token: {token}"

for token in [
    "BH4RheaChEBIReactionExact", "BH4MolecularStoichiometryExact",
    "BH4Atomic369RefinementExact", "BH4ReactionNetworkRunnerReceipt",
    "BH4BiochemicalCrossScaleAdapter", "BH4Chemistry369RunnerRegression",
]:
    assert token in text["focused"], f"missing focused-root token: {token}"
    assert token in text["biology_root"], f"missing external-biology root token: {token}"
    assert token in text["kitzerow_root"], f"missing Kitzerow root token: {token}"

for token in [
    "qdprReactionIsRhea17869", "qdprStoichiometryBalanced",
    "atomicInventoryDoesNotSolveMolecularHamiltonian",
    "coarseBH4ProjectionDoesNotReconstructFineState", "chemistryIsNotLiterally369",
    "coarseNitrogenOxideCannotServeFineChemicalConsumer",
    "runnerDoesNotInventMeasuredFlux",
    "crossScaleAdapterDoesNotCreateAtomsToCellsDerivation",
    "crossScaleAdapterDoesNotCreateDiseaseCausation",
]:
    assert token in text["regression"], f"missing formal regression token: {token}"

print("BH4 chemistry + 369 + runner max-cut regression: ok")
