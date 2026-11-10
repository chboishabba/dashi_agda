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
