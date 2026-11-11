"""Synthetic-only regression of the original-source Agda simplex witness emitter.

This does not replace source-acquired Rhea bytes or Agda kernel validation.
"""
import pytest

from generate_bh4_original29x12_agda import (
    ELEMENTS, fin_constructor, rendered_source_simplex_admission,
)


def sample_elements():
    return {element: [0] * 29 for element in ELEMENTS}


def test_all_29_positive_witnesses_are_source_derived():
    elements = sample_elements()
    for i in range(29):
        elements["H"][i] = i + 1
    lines, status = rendered_source_simplex_admission(elements)
    assert status["all_positive"]
    assert status["zero_weight_species_indices"] == []
    assert status["aggregate_weights"] == list(range(1, 30))
    assert "generatedPositiveSimplexAdmission :" in lines
    assert "generatedPositiveSimplexObstructed :" not in lines
    clauses = [line for line in lines if line.startswith("generatedCHNOPPositiveAt F.")
               or line.startswith("generatedCHNOPPositiveAt (F.")]
    assert len(clauses) == 29
    for i in range(29):
        assert (f"generatedCHNOPPositiveAt {fin_constructor(i)} = "
                f"({i} , refl)") in lines


@pytest.mark.parametrize("index", [0, 1, 14, 28])
def test_zero_atomic_weight_emits_concrete_obstruction(index):
    elements = sample_elements()
    for i in range(29):
        elements["C"][i] = 1
    elements["C"][index] = 0
    lines, status = rendered_source_simplex_admission(elements)
    assert not status["all_positive"]
    assert status["zero_weight_species_indices"] == [index]
    assert f"generatedZeroCHNOPSpecies = {fin_constructor(index)}" in lines
    assert "generatedPositiveSimplexObstructed :" in lines
    assert "generatedPositiveSimplexAdmission :" not in lines
    assert not any(line.startswith("generatedCHNOPPositiveAt ") for line in lines)


@pytest.mark.parametrize("bad", [True, -1, 0.5, "1", None])
def test_bad_source_element_count_rejected(bad):
    elements = sample_elements()
    for i in range(29):
        elements["N"][i] = 1
    elements["N"][10] = bad
    with pytest.raises(ValueError):
        rendered_source_simplex_admission(elements)


def test_missing_axis_and_wrong_species_count_rejected():
    elements = sample_elements()
    del elements["P"]
    with pytest.raises(ValueError):
        rendered_source_simplex_admission(elements)
    elements = sample_elements()
    elements["O"].append(1)
    with pytest.raises(ValueError):
        rendered_source_simplex_admission(elements)


def test_original_charge_source_parser_rejects_fractional_or_boolean():
    # The source checker reuses this exact parser rather than int(...),
    # because signed charge is an integral invariant, not a float cast.
    from run_bh4_reaction_network import _integer
    assert _integer("-2", "charge") == -2
    assert _integer(0, "charge") == 0
    for invalid in (True, False, 1.5, "1.5", "1e0", None, float("nan")):
        with pytest.raises(ValueError):
            _integer(invalid, "charge")


def test_original_rational_producer_is_source_definitional_and_covers_72_columns():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines = rendered_source_rational_producer()
    assert "generatedRationalReactants =" in lines
    assert "generatedRationalProducts =" in lines
    assert any("generatedColumns" in line for line in lines)
    assert any("Panel.originalReactants column" in line for line in lines)
    assert any("Panel.originalProducts column" in line for line in lines)
    clauses = [line for line in lines if line.startswith(
        "generatedRationalColumnsBalance F.")
        or line.startswith("generatedRationalColumnsBalance (F.")]
    assert len(clauses) == 72
    assert len(set(clauses)) == 72
    assert all("QP.≃-reflexive refl" in clause for clause in clauses)
    assert "generatedOriginalSixAxisRationalProducer rates fluxes =" in lines
    assert "generatedOriginalSixAxisBishopProducer rates fluxes =" in lines
    assert any("Composer.originalSixAxisNativeAndReactionBalance" in line
               for line in lines)
    assert any("Composer.originalSixAxisNativeReactionBalanceBishop" in line
               for line in lines)
    assert not any("postulate" in line for line in lines)


def test_original_rational_source_generated_proof_axes_not_reinterpreted_as_measured():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines=rendered_source_rational_producer()
    assert any("generatedPositiveCharges generatedNegativeCharges" in line
               for line in lines)
    assert any("generatedElementWeights Panel.carbonElement" in line
               for line in lines)
    assert any("generatedElementWeights Panel.phosphorusElement" in line
               for line in lines)
    assert "generatedRationalAxes : V.Vec (V.Vec Q.ℚᵘ 29) 6" in lines
    assert "  (rates : V.Vec (V.Vec Q.ℚᵘ 12) 27)" in lines
    assert "  (fluxes : V.Vec (V.Vec Q.ℚᵘ 29) 54)" in lines


def test_generated_original_rhs_uses_same_source_stoichiometry_and_native_incidence():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines=rendered_source_rational_producer()
    assert "generatedRationalStoichiometry : Operator.Matrix 29 12" in lines
    assert "generatedRationalStoichiometry =" in lines
    assert "      (V.lookup (V.lookup generatedRationalProducts column) species)" in lines
    assert "      (V.lookup (V.lookup generatedRationalReactants column) species)))" in lines
    assert "generatedOriginalRationalInputs fluxes rates =" in lines
    assert "  NativeGeometry.originalNativeRationalInputs" in lines
    assert "    fluxes generatedRationalStoichiometry rates" in lines
    assert "generatedOriginalRationalRHS fluxes rates =" in lines
    assert "  Operator.rational369SemidiscreteRHS" in lines
    assert "generatedOriginalRationalRHSAt fluxes rates site species =" in lines
    assert "  Operator.rational369SemidiscreteAt" in lines
    # This is a 783-coordinate operator, not a global-zero assumption.
    assert "  Operator.Matrix 27 12 → Operator.Matrix 27 29" in lines
    assert not any("source_kinetic_parameters_authenticated = true" in line
                   for line in lines)


def test_generated_actual_783_rhs_bishop_proof_has_no_global_zero_input():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines=rendered_source_rational_producer()
    net=[line for line in lines if line.startswith(
        "generatedRationalNetColumnsZero F.")
        or line.startswith("generatedRationalNetColumnsZero (F.")]
    assert len(net)==72 and len(set(net))==72
    assert all("QP.≃-reflexive refl" in line for line in net)
    assert "generatedRationalNetColumnsZero :" in lines
    assert "generatedOriginalComputedSixAxisBishopConservation :" in lines
    assert "generatedOriginalComputedSixAxisBishopConservation fluxes rates =" in lines
    assert "  NativeComputed.originalNativeComputedSixAxisBishopConserves" in lines
    assert "      Kernel.originalReactionAllSitesZeroFromSourceColumns" in lines
    assert "        (generatedRationalNetColumnsZero axis))" in lines
    assert not any("postulate" in line or "globalZero :"
                   in line for line in lines)


def test_original_generator_exposes_only_proof_candidate_not_kernel_receipt():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines=rendered_source_rational_producer()
    assert any("generatedRationalStoichiometry" in line for line in lines)
    assert any("generatedOriginalRationalRHS fluxes rates" in line
               for line in lines)
    assert not any("agda_kernel_checked = true" in line
                   for line in lines)


def test_original_source_reaction_conserves_all_six_axes_at_arbitrary_bishop_rates():
    from generate_bh4_original29x12_agda import rendered_source_rational_producer
    lines=rendered_source_rational_producer()
    assert "generatedOriginalBishopAnyReactionRatesConserve :" in lines
    assert "generatedOriginalBishopAnyReactionRatesConserve rates axis =" in lines
    assert "  BishopRates.original369BishopArbitraryReactionRatesConserve" in lines
    assert "    rates (generatedRationalColumnsBalance axis)" in lines
    assert "  (rates : V.Vec (V.Vec R.ℝ 12) 27)" in lines
    assert "  (axis : F.Fin 6) →" in lines
    assert all("source_rhea_kinetics_paid" not in line for line in lines)
