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
