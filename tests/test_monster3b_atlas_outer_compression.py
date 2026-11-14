from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from analyze_monster3b_symplectic_compressions import analyze_split_sources, parse_meataxe_file

DATA = ROOT / "data" / "atlas"
INNER = [DATA / "2SuzG1-f3r12B0.m1", DATA / "2SuzG1-f3r12B0.m2"]
OUTER = [DATA / "2Suzd2G1-f3r12aB0.m1", DATA / "2Suzd2G1-f3r12aB0.m2"]


def test_atlas_outer_pair_has_field_and_heisenberg_source_words():
    result = analyze_split_sources(
        [parse_meataxe_file(path) for path in INNER],
        [parse_meataxe_file(path) for path in OUTER],
        depth=8,
    )
    assert result["invariant_alternating_form_space_dimension"] == 1
    assert result["outer_similitude_multipliers"] == [2, 1]
    assert result["outer_generator_2_equals_inner_generator_2"] is True

    # Earlier strict-symplectic field-algebra selector.
    depth5 = next(row for row in result["irreducible_degree6_compression_hits"]
                  if row["word"] == "g2 g1 g2^-1 g1 g2^-1")
    assert depth5["source_similitude_multiplier"] == 1
    assert depth5["cyclic_rank_e0"] == 6
    assert depth5["heisenberg_cocycle_defect_symmetric"] is True

    # Primitive multiplier-2 word: useful for the full normalizer / phase swap.
    depth7 = next(row for row in result["irreducible_degree6_compression_hits"]
                  if row["word"] == "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1")
    assert depth7["source_similitude_multiplier"] == 2
    assert depth7["compression_charpoly"] == "x**6 - x**5 - x**4 - x**3 + x**2 - 1"
    assert depth7["heisenberg_cocycle_defect_symmetric"] is True
    assert depth7["heisenberg_center_correction_constructed"] is True

    # Strongest same-phase field target: strict symplectic AND primitive in the
    # selected GF(729) under the downstream receipt.
    depth8 = next(row for row in result["irreducible_degree6_compression_hits"]
                  if row["word"] == "g1 g2^-1 g1 g2 g1 g2^-1 g1 g2^-1")
    assert depth8["source_similitude_multiplier"] == 1
    assert depth8["compression_charpoly"] == "x**6 - x**4 + x**2 - x - 1"
    assert depth8["compression_matrix"] == [
        [2,2,0,1,1,2],
        [0,0,0,1,1,2],
        [2,1,0,0,0,0],
        [1,2,0,2,2,2],
        [0,0,1,1,1,2],
        [0,0,1,2,1,1],
    ]
    assert depth8["cyclic_rank_e0"] == 6
    assert depth8["breaks_swap01_at_e0"] is True
    assert depth8["stabilises_translation_lagrangian"] is False
    assert depth8["heisenberg_cocycle_defect_symmetric"] is True
    assert depth8["heisenberg_center_correction_constructed"] is True
    assert depth8["heisenberg_cocycle_defect_matrix"] == [
        [2,2,0,1,2,0,2,1,0,0,0,2],
        [2,2,2,2,0,1,0,2,0,2,1,1],
        [0,2,0,2,2,2,2,2,1,2,1,1],
        [1,2,2,2,0,1,0,2,0,1,2,0],
        [2,0,2,0,1,0,2,0,2,2,2,1],
        [0,1,2,1,0,1,2,2,1,2,1,0],
        [2,0,2,0,2,2,0,1,2,2,0,0],
        [1,2,2,2,0,2,1,1,1,1,2,1],
        [0,0,1,0,2,1,2,1,2,0,1,2],
        [0,2,2,1,2,2,2,1,0,1,1,1],
        [0,1,1,2,2,1,0,2,1,1,2,2],
        [2,1,1,0,1,0,0,1,2,1,2,2],
    ]
