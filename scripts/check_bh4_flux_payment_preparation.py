from pathlib import Path

root = Path(__file__).resolve().parents[1]
script = root / "scripts/prepare_bh4_flux_payment.py"
runner = root / "scripts/run_bh4_phase4_maxcut.py"
formal = root / "DASHI/Biology/BH4FluxPaymentPreparationExact.agda"

for p in [script, runner, formal]:
    assert p.exists(), f"missing flux-payment preparation owner: {p.relative_to(root)}"

s = script.read_text()
for token in [
    "dashi.bh4-flux-payment-preparation.v1",
    "assay-specific-capacity",
    "turnover-capacity",
    "kinetic-shape-only",
    "primary-literature-gap",
    "enzyme_abundance_required",
    "normalization_bridge_required",
    "assay_condition_translation_required",
    "steady_state_flux_bound_payable",
    "rate_candidate_creates_intracellular_flux",
    "specific_activity_creates_compartment_flux",
    "kcat_creates_flux_without_abundance",
]:
    assert token in s, f"missing payment-preparation token: {token}"

r = runner.read_text()
for token in ["prepare_bh4_flux_payment.py", "bh4-flux-payment-preparation.json", "sabio_flux_payment"]:
    assert token in r, f"runner missing flux-payment preparation token: {token}"

f = formal.read_text()
for token in [
    "BH4FluxEvidenceClass",
    "assaySpecificCapacity",
    "turnoverCapacity",
    "kineticShapeOnly",
    "primaryLiteratureGap",
    "specificActivityCreatesCompartmentFlux",
    "kcatCreatesFluxWithoutAbundance",
    "shapeParameterCreatesMagnitudeBound",
]:
    assert token in f, f"formal payment owner missing token: {token}"

print("BH4 flux payment preparation regression: ok")
