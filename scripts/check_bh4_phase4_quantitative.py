from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "evidence": root / "DASHI/Biology/BH4QuantitativeAcquisitionExact.agda",
    "sifts_receipt": root / "DASHI/Biology/BH4ExecutedSIFTSReceiptExact.agda",
    "solver": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "sabio": root / "scripts/acquire_bh4_sabio_kinetics.py",
    "sifts": root / "scripts/acquire_bh4_pdbe_sifts.py",
    "parameters": root / "scripts/acquire_bh4_parameter_evidence.py",
    "interval_solver": root / "scripts/solve_bh4_flux_intervals.py",
    "runner": root / "scripts/run_bh4_phase4_maxcut.py",
    "runbook": root / "docs/biology/BH4Phase4QuantitativeRunbook.md",
    "phase4_checker": root / "scripts/check_bh4_phase4_system_state.py",
    "unified": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing quantitative max-cut {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in [
    "SABIO", "PDBe", "SIFTS", "browserShellPayload",
    "firstSABIOAttemptMayConcludeZeroEntries = false",
    "pdbeSiftsBoundedAcquisitionExecuted = true",
    "kineticConstantCreatesFluxBound", "htmlShellCreatesNoEntryConclusion",
    "structureMappingCreatesCatalyticMechanism", "boundedSIFTSAcquisitionCreatesSiteFunction",
    "sourceSpecificEvidenceRequired",
]:
    assert token in text["evidence"], f"missing quantitative evidence token: {token}"

for token in [
    "structuresExamined = 38", "matchingSIFTSSegmentCount = 526",
    "proteinsWithUniProtPDBLinks = 14", "proteinsWithMatchingSegments = 13",
    "PCBD1", "AGMO", "PAH", "mappingCreatesCatalyticFunction",
]:
    assert token in text["sifts_receipt"], f"missing executed SIFTS receipt token: {token}"

for token in [
    "rerunSABIOAfterProtocolRepair", "adjudicateSABIOKineticCandidatesIntoFluxBounds",
    "adjudicatePDBSIFTSResidueSiteWitnesses", "firstBoundedSIFTSAcquisitionExecuted",
    "sabioProtocolRepairReady = true", "expandedQuantitativeCoordinateCount = 56",
]:
    assert token in text["roadmap"], f"missing quantitative roadmap token: {token}"

for token in [
    "IntervalFluxSolverStatus", "solverUnavailable", "underdetermined",
    "feasible", "infeasible", "missingExchangeBoundMayBeSubstitutedWithZero",
    "feasibleSteadyStateCreatesDiseaseMechanism",
]:
    assert token in text["solver"], f"missing interval solver token: {token}"

for token in [
    "https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json",
    "UniProtKB_AC", "meta", "total_count", "data", "pageSize",
    "dashi.bh4-sabio-kinetics.v3", "export-envelope",
    "kinetic_parameters_create_flux_bounds",
]:
    assert token in text["sabio"], f"missing SABIO export-api token: {token}"

for token in [
    "SIFTS", "uniprot_pdb", "pdb_chain_uniprot", "raw_sha256",
    "matching_sifts_segment_count", "structures_examined", "summarize",
    "dashi.bh4-pdbe-sifts.v2", "structure_mapping_creates_catalytic_mechanism",
]:
    assert token in text["sifts"], f"missing SIFTS summary token: {token}"

for token in ["EXCHANGE:", "reaction_flux_ids", "exchange_ids", "dashi.bh4-parameter-evidence.v2"]:
    assert token in text["parameters"], f"missing parameter exchange token: {token}"

for token in [
    "scipy.optimize", "linprog", "REACTION_FLUX:", "EXCHANGE:",
    "solver-unavailable", "underdetermined", "candidate_flux_balance_witness",
]:
    assert token in text["interval_solver"], f"missing solver script token: {token}"

for token in [
    "acquire_rhea_chebi_bh4_reactions.py", "build_bh4_stoichiometric_matrix.py",
    "acquire_bh4_sabio_kinetics.py", "acquire_bh4_pdbe_sifts.py",
    "solve_bh4_flux_intervals.py", "bh4-phase4-maxcut-summary.json",
]:
    assert token in text["runner"], f"missing one-command runner token: {token}"

for token in ["56 coordinates", "S*v + e = 0", "SABIO-RK", "PDBe/SIFTS", "bh4-phase4-maxcut-summary.json", "check_kitzerow_bh4_priority_all.py"]:
    assert token in text["runbook"], f"missing runbook token: {token}"

for root_name in ["phase4_checker", "unified"]:
    for token in ["BH4QuantitativeAcquisitionExact", "BH4IntervalFluxSolverExact"]:
        assert token in text[root_name], f"missing {root_name} quantitative import/token: {token}"

print("BH4 Phase-4 quantitative acquisition + interval solver regression: ok")
