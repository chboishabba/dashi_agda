from pathlib import Path

root = Path(__file__).resolve().parents[1]

files = {
    "evidence": root / "DASHI/Biology/BH4QuantitativeAcquisitionExact.agda",
    "sabio_receipt": root / "DASHI/Biology/BH4ExecutedSABIOReceiptExact.agda",
    "sabio_adjudication_receipt": root / "DASHI/Biology/BH4ExecutedSABIOAdjudicationReceiptExact.agda",
    "gap_evidence": root / "DASHI/Biology/BH4MissingReactionKineticsEvidenceExact.agda",
    "sifts_receipt": root / "DASHI/Biology/BH4ExecutedSIFTSReceiptExact.agda",
    "solver": root / "DASHI/Biology/BH4IntervalFluxSolverExact.agda",
    "roadmap": root / "DASHI/Biology/BH4Phase4RoadmapExact.agda",
    "rhea": root / "scripts/acquire_rhea_chebi_bh4_reactions.py",
    "sabio": root / "scripts/acquire_bh4_sabio_kinetics.py",
    "sabio_adjudication": root / "scripts/build_bh4_sabio_adjudication.py",
    "sifts": root / "scripts/acquire_bh4_pdbe_sifts.py",
    "parameters": root / "scripts/acquire_bh4_parameter_evidence.py",
    "interval_solver": root / "scripts/solve_bh4_flux_intervals.py",
    "runner": root / "scripts/run_bh4_phase4_maxcut.py",
    "runbook": root / "docs/biology/BH4Phase4QuantitativeRunbook.md",
    "phase4_checker": root / "DASHI/Biology/BH4Phase4SystemStateRegression.agda",
    "unified": root / "DASHI/Unified/BH4BiochemicalEverything.agda",
}

for name, path in files.items():
    assert path.exists(), f"missing quantitative max-cut {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}

for token in ["kineticConstantCreatesFluxBound", "structureMappingCreatesCatalyticMechanism", "sourceSpecificEvidenceRequired"]:
    assert token in text["evidence"], f"missing quantitative evidence token: {token}"

for token in ["executedSABIOKineticEntryCount", "executedSABIOKineticParameterCount", "190", "932", "11", "parameterObjectCreatesInVivoFluxBound"]:
    assert token in text["sabio_receipt"], f"missing executed SABIO receipt token: {token}"

for token in ["executedParameterCandidateCount", "executedMappedParameterCandidateCount", "executedFiniteReactionCoverage", "932", "875", "10", "RHEA:11920", "RHEA:19897", "affinityLikeCount", "rateLikeCount", "turnoverLikeCount", "unclassifiedCount", "candidateCoverageCreatesFluxPayment"]:
    assert token in text["sabio_adjudication_receipt"], f"missing executed SABIO adjudication receipt token: {token}"

for token in ["PCBD1", "NOS", "RHEA:11920", "RHEA:19897", "10.1073/pnas.92.26.12384", "10.1111/j.1432-1033.1995.tb20714.x", "PMID:9224737", "PMID:9089781", "primaryKineticsCreatesNetworkFluxBound"]:
    assert token in text["gap_evidence"], f"missing gap-evidence token: {token}"

for token in ["executedStructuresExamined = 38", "executedMatchingSIFTSSegmentCount = 526", "mappingCreatesCatalyticFunction"]:
    assert token in text["sifts_receipt"], f"missing executed SIFTS receipt token: {token}"

for token in ["acquireMissingPCBD1NOSPrimaryKinetics", "adjudicateSABIOKineticCandidatesIntoFluxBounds", "adjudicatePDBSIFTSResidueSiteWitnesses", "sabioExportAcquisitionExecuted", "sabioKineticParameterCount", "sabioFiniteReactionCandidateCoverage", "expandedQuantitativeCoordinateCount = 56"]:
    assert token in text["roadmap"], f"missing quantitative roadmap token: {token}"

for token in ["NETWORK_ATTEMPTS = 3", "NETWORK_BACKOFF_SECONDS", "_retry", "network_retry_exhaustion_means_reaction_absent"]:
    assert token in text["rhea"], f"missing Rhea retry hardening token: {token}"

for token in ["IntervalFluxSolverStatus", "solverUnavailable", "underdetermined", "missingExchangeBoundMayBeSubstitutedWithZero"]:
    assert token in text["solver"], f"missing interval solver token: {token}"

for token in ["https://sabio.h-its.org/export-api/sabio/kinlaw-entry/json", "UniProtKB_AC", "dashi.bh4-sabio-kinetics.v3", "n_start_value", "n_end_value", "kinetic_parameter_candidates", "kinetic_parameters_create_flux_bounds"]:
    assert token in text["sabio"], f"missing SABIO export-api/parameter token: {token}"

for token in ["dashi.bh4-sabio-adjudication.v2", "finite_matrix_rhea_ids", "usable_for_flux_bound", "parameter_kind_hint", "sbo_term", "catalytic-constant-like", "inhibitory-like", "concentration-like", "uncovered_finite_reactions", "parameter_candidate_creates_flux_bound"]:
    assert token in text["sabio_adjudication"], f"missing SABIO adjudication token: {token}"

for token in ["matching_sifts_segment_count", "structures_examined", "dashi.bh4-pdbe-sifts.v2", "structure_mapping_creates_catalytic_mechanism"]:
    assert token in text["sifts"], f"missing SIFTS summary token: {token}"

for token in ["EXCHANGE:", "REACTION_FLUX:", "dashi.bh4-parameter-evidence.v2"]:
    assert token in text["parameters"], f"missing parameter exchange token: {token}"

for token in ["scipy.optimize", "linprog", "REACTION_FLUX:", "EXCHANGE:", "solver-unavailable", "underdetermined"]:
    assert token in text["interval_solver"], f"missing solver script token: {token}"

for token in ["acquire_rhea_chebi_bh4_reactions.py", "build_bh4_stoichiometric_matrix.py", "acquire_bh4_sabio_kinetics.py", "build_bh4_sabio_adjudication.py", "acquire_bh4_pdbe_sifts.py", "solve_bh4_flux_intervals.py", "bh4-sabio-adjudication.json", "bh4-phase4-maxcut-summary.json"]:
    assert token in text["runner"], f"missing one-command runner token: {token}"

for token in ["56-coordinate", "S*v + e = 0", "SABIO-RK", "PDBe/SIFTS", "932", "875", "10 of 12", "bh4-phase4-maxcut-summary.json", "check_kitzerow_bh4_priority_all.py"]:
    assert token in text["runbook"], f"missing runbook token: {token}"

for root_name in ["phase4_checker", "unified"]:
    for token in ["BH4ExecutedSABIOAdjudicationReceiptExact", "BH4MissingReactionKineticsEvidenceExact", "BH4QuantitativeAcquisitionExact", "BH4IntervalFluxSolverExact"]:
        assert token in text[root_name], f"missing {root_name} quantitative import/token: {token}"

print("BH4 Phase-4 quantitative acquisition + interval solver regression: ok")
