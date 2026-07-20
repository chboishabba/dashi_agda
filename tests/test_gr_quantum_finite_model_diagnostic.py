from __future__ import annotations

import importlib.util
from pathlib import Path


ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts" / "run_gr_quantum_finite_model_diagnostic.py"


def load_diagnostic_module():
    spec = importlib.util.spec_from_file_location("gr_quantum_finite_diagnostic", SCRIPT)
    assert spec is not None
    assert spec.loader is not None
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_finite_gr_quantum_diagnostic_passes_all_bounded_checks():
    module = load_diagnostic_module()
    report = module.build_report()

    assert report["all_finite_checks_pass"] is True
    assert report["terminal_unification_claim"] is False
    assert report["physical_validation_claim"] is False


def test_quaternion_cover_is_exactly_two_to_one():
    module = load_diagnostic_module()
    receipt = module.check_quaternion_cover()

    assert receipt["homomorphism_holds"] is True
    assert receipt["all_fibers_size_two"] is True
    assert receipt["kernel_is_plus_minus_one"] is True
    assert receipt["group_size"] == 8
    assert receipt["rotation_size"] == 4


def test_quadratic_and_weyl_receipts_are_unique_and_exact():
    module = load_diagnostic_module()

    quadratic = module.check_quadratic_uniqueness()
    weyl = module.check_qutrit_weyl()

    assert quadratic["satisfying_tables"] == [[0, 1, 1, 2]]
    assert quadratic["unique_in_search"] is True
    assert weyl["weyl_shift_holds"] is True
    assert weyl["shift_cubed_identity"] is True


def test_regulated_spectrum_stays_fail_closed():
    module = load_diagnostic_module()
    spectrum = module.check_regulated_spectrum()

    assert spectrum["finite"] is True
    assert spectrum["regional_basis_dimension"] == 9
    assert spectrum["physical_low_energy_match_supplied"] is False
