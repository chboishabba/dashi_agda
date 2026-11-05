import importlib.util
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "verify_monster3b_schrodinger_character.py"


def load_module():
    spec = importlib.util.spec_from_file_location("schrodinger_character", SCRIPT)
    module = importlib.util.module_from_spec(spec)
    assert spec.loader is not None
    spec.loader.exec_module(module)
    return module


def test_literal_character_audit():
    m = load_module()
    receipt = m.audit()

    assert receipt["heisenberg_order"] == 3**13
    assert receipt["basis_degree"] == 729
    assert receipt["identity_count"] == 1
    assert receipt["central_zeta_count"] == 1
    assert receipt["central_zeta_squared_count"] == 1
    assert receipt["noncentral_count"] == 3**13 - 3

    assert receipt["nonzero_translation_count"] == 1592136
    assert receipt["pure_nonzero_modulation_count"] == 2184
    assert receipt["nonzero_translation_count"] + receipt["pure_nonzero_modulation_count"] == receipt["noncentral_count"]

    assert receipt["all_729_modulation_character_sums_verified"] is True
    assert receipt["all_1594323_group_coordinates_classified"] is True
    assert receipt["literal_character_equals_canonical_heisenberg_signature"] is True

    assert receipt["identity_trace"] == [729, 0]
    assert receipt["central_zeta_trace"] == [0, 729]
    assert receipt["central_zeta_squared_trace"] == [-729, -729]
    assert receipt["noncentral_trace"] == [0, 0]
