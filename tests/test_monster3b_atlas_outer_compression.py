from pathlib import Path
import sys

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))

from analyze_monster3b_symplectic_compressions import analyze_split_sources, parse_meataxe_file


DATA = ROOT / "data" / "atlas"
INNER = [DATA / "2SuzG1-f3r12B0.m1", DATA / "2SuzG1-f3r12B0.m2"]
OUTER = [DATA / "2Suzd2G1-f3r12aB0.m1", DATA / "2Suzd2G1-f3r12aB0.m2"]


def test_atlas_outer_pair_has_degree_six_x6_compressions_and_heisenberg_correction():
    result = analyze_split_sources(
        [parse_meataxe_file(path) for path in INNER],
        [parse_meataxe_file(path) for path in OUTER],
        depth=7,
    )

    assert result["invariant_alternating_form_space_dimension"] == 1
    assert result["outer_similitude_multipliers"] == [2, 1]
    assert result["outer_generator_2_equals_inner_generator_2"] is True

    depth5 = next(
        row for row in result["irreducible_degree6_compression_hits"]
        if row["word"] == "g2 g1 g2^-1 g1 g2^-1"
    )
    assert depth5["compression_charpoly"] == "x**6 - x**5 - x**3 + x**2 + 1"
    assert depth5["cyclic_rank_e0"] == 6
    assert depth5["breaks_swap01_at_e0"] is True
    assert depth5["stabilises_translation_lagrangian"] is False

    depth7 = next(
        row for row in result["irreducible_degree6_compression_hits"]
        if row["word"] == "g2^-1 g1 g2^-1 g1 g2 g1 g2^-1"
    )
    assert depth7["compression_charpoly"] == "x**6 - x**5 - x**4 - x**3 + x**2 - 1"
    assert depth7["compression_matrix"] == [
        [0, 0, 0, 2, 2, 2],
        [2, 1, 0, 2, 0, 0],
        [0, 2, 1, 0, 0, 2],
        [1, 0, 1, 0, 2, 0],
        [2, 0, 2, 2, 0, 1],
        [0, 1, 1, 2, 0, 2],
    ]
    assert depth7["cyclic_rank_e0"] == 6
    assert depth7["breaks_swap01_at_e0"] is True
    assert depth7["stabilises_translation_lagrangian"] is False

    # The preferred word is a multiplier-2 symplectic similitude.  Its
    # asymmetric-cocycle defect is symmetric, hence admits the quadratic
    # center correction q(x)=2*B(x,x) used by the generalized lift.
    assert depth7["source_similitude_multiplier"] == 2
    assert depth7["heisenberg_cocycle_defect_symmetric"] is True
    assert depth7["heisenberg_center_correction_constructed"] is True
    assert depth7["heisenberg_cocycle_defect_matrix"] == [
        [2,0,2,2,1,0,2,1,1,2,2,0],
        [0,1,2,1,2,1,2,1,2,2,0,2],
        [2,2,1,2,2,0,2,1,0,1,0,1],
        [2,1,2,0,0,1,0,0,0,1,2,0],
        [1,2,2,0,1,2,1,0,0,1,1,0],
        [0,1,0,1,2,0,0,2,1,2,1,1],
        [2,2,2,0,1,0,1,0,2,1,0,2],
        [1,1,1,0,0,2,0,1,1,2,0,0],
        [1,2,0,0,0,1,2,1,1,2,2,2],
        [2,2,1,1,1,2,1,2,2,0,0,0],
        [2,0,0,2,1,1,0,0,2,0,1,1],
        [0,2,1,0,0,1,2,0,2,0,1,1],
    ]
