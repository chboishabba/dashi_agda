#!/usr/bin/env python3
"""Static regression for Phase-4 state/payment acquisition max-cut."""
from pathlib import Path

root = Path(__file__).resolve().parents[1]
files = {
    "abundance": root / "scripts/acquire_bh4_protein_abundance.py",
    "exchange": root / "scripts/acquire_bh4_exchange_context.py",
    "compiler": root / "scripts/build_bh4_joint_payment_ledger.py",
    "formal": root / "DASHI/Biology/BH4JointPaymentAcquisitionExact.agda",
    "regression": root / "DASHI/Biology/BH4JointPaymentAcquisitionRegression.agda",
    "runner": root / "scripts/run_bh4_phase4_maxcut.py",
}
for name, path in files.items():
    assert path.exists(), f"missing BH4 state/payment acquisition {name}: {path.relative_to(root)}"

text = {name: path.read_text() for name, path in files.items()}
for token in [
    "proteomicsdb.org",
    "proteinexpression.xsodata",
    "NORMALIZED_INTENSITY",
    "CALCULATION_METHOD=0",
    "cell%20line",
    "abundance_candidate_creates_enzyme_concentration",
    "same_tissue_required",
]:
    assert token in text["abundance"], f"missing abundance token: {token}"
for token in [
    "metabolomicsworkbench.org/rest",
    "/refmet/name/",
    "/refmet/match/",
    "/metstat/;;;Human;;;;",
    "canonical_refmet_name",
    "concentration_context_creates_exchange_flux",
    "exchange_flux_requires_transport_or_turnover_evidence",
]:
    assert token in text["exchange"], f"missing exchange-context token: {token}"
for token in [
    "dashi.bh4-joint-payment-ledger.v1",
    "reaction_flux_coordinates",
    "exchange_coordinates",
    "state_context_coordinates",
    "solver_payable",
    "concentration_context_is_not_exchange_flux",
    "abundance_intensity_is_not_enzyme_concentration",
]:
    assert token in text["compiler"], f"missing joint-payment compiler token: {token}"
for token in [
    "BH4JointPaymentAcquisitionBoundary",
    "proteinIntensityCreatesEnzymeConcentration",
    "metaboliteConcentrationCreatesExchangeFlux",
    "sameObjectContextMayBeDropped",
    "contextCoverageCreatesSolverPayment",
]:
    assert token in text["formal"], f"missing formal joint-payment token: {token}"
for token in [
    "bh4-protein-abundance.json",
    "bh4-exchange-context.json",
    "bh4-joint-payment-ledger.json",
    "dashi.bh4-phase4-maxcut-run.v8",
    "protein_abundance",
    "exchange_context",
    "joint_payment",
]:
    assert token in text["runner"], f"missing runner state-payment token: {token}"
print("BH4 state/payment acquisition max-cut regression: ok")
