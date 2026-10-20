from pathlib import Path

root = Path(__file__).resolve().parents[1]

ranking = root / "scripts/rank_bh4_flux_candidates.py"
runner = root / "scripts/run_bh4_phase4_maxcut.py"
roadmap = root / "DASHI/Biology/BH4Phase4RoadmapExact.agda"
receipt = root / "DASHI/Biology/BH4ExecutedSABIOAdjudicationReceiptExact.agda"

for path in [ranking, runner, roadmap, receipt]:
    assert path.exists(), f"missing BH4 flux candidate ranking surface: {path.relative_to(root)}"

rank_text = ranking.read_text()
run_text = runner.read_text()
roadmap_text = roadmap.read_text()
receipt_text = receipt.read_text()

for token in [
    "dashi.bh4-flux-candidate-ranking.v1",
    "direct-rate-candidate",
    "capacity-candidate",
    "kinetic-shape-candidate",
    "assay-context-only",
    "not-flux-informative",
    "assay_reaction_identity_paid",
    "same_object_compartment_time_paid",
    "normalized_solver_flux_unit_paid",
    "kinetic_to_flux_translation_paid",
    "usable_for_flux_bound",
    "top_candidates_by_reaction",
    "blocked_reaction_count",
    "payable_reaction_count",
]:
    assert token in rank_text, f"missing ranking token: {token}"

for token in [
    "bh4-flux-candidate-ranking.json",
    "rank_bh4_flux_candidates.py",
    "sabio_flux_ranking",
    "dashi.bh4-phase4-maxcut-run.v5",
]:
    assert token in run_text, f"missing runner ranking token: {token}"

for token in [
    "sabioKineticParameterCount",
    "sabioMappedParameterCandidates",
    "sabioFiniteReactionCandidateCoverage",
    "rankSABIOCandidatesByFluxRelevance",
]:
    assert token in roadmap_text, f"missing roadmap ranking token: {token}"

for token in ["932", "875", "10", "RHEA:11920", "RHEA:19897"]:
    assert token in receipt_text, f"missing executed adjudication receipt token: {token}"

print("BH4 flux candidate ranking regression: ok")
