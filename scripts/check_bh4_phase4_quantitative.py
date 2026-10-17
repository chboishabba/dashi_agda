from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "evidence": root / "DASHI/Biology/BH4QuantitativeAcquisitionExact.agda",
    "solver": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "sabio": root / "scripts/acquire_bh4_sabio_kinetics.py",
    "sifts": root / "scripts/acquire_bh4_pdbe_sifts.py",
    "parameters": root / "scripts/acquire_bh4_parameter_evidence.py",
    "interval_solver": root / "scripts/solve_bh4_flux_intervals.py",
    "phase4_checker": root / "scripts/check_bh4_phase4_system_state.py",
    "unified": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing quantitative max-cut {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in [
    "SABIO", "PDBe", "SIFTS", "kineticConstantCreatesFluxBound",
    "structureMappingCreatesCatalyticMechanism", "sourceSpecificEvidenceRequired",
]:
    assert token in text["evidence"], f"missing quantitative evidence token: {token}"

for token in [
    "IntervalFluxSolverStatus", "solverUnavailable", "underdetermined",
    "feasible", "infeasible", "missingExchangeBoundMayBeSubstitutedWithZero",
    "feasibleSteadyStateCreatesDiseaseMechanism",
]:
    assert token in text["solver"], f"missing interval solver token: {token}"

for token in [
    "UniProtKB_AC", "kineticlawsExportTsv", "Parameter", "PubMedID",
    "raw_sha256", "kinetic_parameters_create_flux_bounds",
]:
    assert token in text["sabio"], f"missing SABIO token: {token}"

for token in [
    "SIFTS", "uniprot_pdb", "pdb_chain_uniprot", "raw_sha256",
    "structure_mapping_creates_catalytic_mechanism",
]:
    assert token in text["sifts"], f"missing SIFTS token: {token}"

for token in ["EXCHANGE:", "reaction_flux_ids", "exchange_ids"]:
    assert token in text["parameters"], f"missing parameter exchange token: {token}"

for token in [
    "scipy.optimize", "linprog", "REACTION_FLUX:", "EXCHANGE:",
    "solver-unavailable", "underdetermined", "candidate_flux_balance_witness",
]:
    assert token in text["interval_solver"], f"missing solver script token: {token}"

for root_name in ["phase4_checker", "unified"]:
    for token in ["BH4QuantitativeAcquisitionExact", "BH4IntervalFluxSolverExact"]:
        assert token in text[root_name], f"missing {root_name} quantitative import/token: {token}"

print("BH4 Phase-4 quantitative acquisition + interval solver regression: ok")
