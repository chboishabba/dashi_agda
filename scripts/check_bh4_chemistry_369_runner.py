from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "reaction": root / "DASHI/Biology/Molecular/BH4RheaChEBIReactionExact.agda",
    "stoich": root / "DASHI/Biology/Molecular/BH4MolecularStoichiometryExact.agda",
    "refinement": root / "DASHI/Interop/BH4Atomic369RefinementExact.agda",
    "runner_receipt": root / "DASHI/Biology/BH4ReactionNetworkRunnerReceipt.agda",
    "runner": root / "scripts/run_bh4_reaction_network.py",
    "unified": root / "DASHI/Unified/BH4BiochemicalCrossScaleAdapter.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing {name}: {path.relative_to(root)}"

reaction = files["reaction"].read_text()
stoich = files["stoich"].read_text()
refinement = files["refinement"].read_text()
runner_receipt = files["runner_receipt"].read_text()
runner = files["runner"].read_text()
unified = files["unified"].read_text()

for token in [
    "RHEA:17869", "RHEA:32253", "CHEBI:15372", "CHEBI:57540",
    "CHEBI:30156", "CHEBI:57945", "CHEBI:15378",
    "reactionIdentityCreatesBiologicalMechanism",
]:
    assert token in reaction, f"missing reaction token: {token}"

for token in [
    "qdprAtomAndChargeBalanced", "balancedReactionCreatesKineticLaw",
    "balancedReactionCreatesDiseaseMechanism", "MolecularStoichiometricConservation",
]:
    assert token in stoich, f"missing stoichiometry token: {token}"

for token in [
    "AtomicGenerationPipelineExact", "ArgumentLevelTransportHyperformalismExact",
    "atomicInventorySolvesMolecularHamiltonian",
    "coarseBH4AvailabilityReconstructsFineChemicalState",
    "chemistryIsLiterally369",
]:
    assert token in refinement, f"missing refinement token: {token}"

for token in [
    "stoichiometricRunnerCreatesMeasuredFlux", "runnerStateCreatesDiseaseMechanism",
    "BH4SystemState", "reactionIdentityPaid", "wholeSystemFluxMeasured",
]:
    assert token in runner_receipt, f"missing runner receipt token: {token}"

for token in [
    "rhea_id", "stoichiometrically_balanced", "kinetics_supplied",
    "measured_flux_promoted", "disease_mechanism_promoted", "residuals",
]:
    assert token in runner, f"missing runner token: {token}"

for token in [
    "CrossScaleMatterPhysics", "PhysicsChemistryBiologyDNAUnificationDischarge",
    "adapterCreatesFirstPrinciplesAtomsToCellsDerivation",
    "adapterCreatesDiseaseCausation",
]:
    assert token in unified, f"missing unified adapter token: {token}"

print("BH4 chemistry + 369 + runner max-cut regression: ok")
