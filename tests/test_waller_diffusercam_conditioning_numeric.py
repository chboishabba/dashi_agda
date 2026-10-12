from importlib.util import module_from_spec, spec_from_file_location
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SCRIPT = ROOT / "scripts/check_waller_diffusercam_conditioning.py"


def load_audit_module():
    spec = spec_from_file_location("waller_conditioning", SCRIPT)
    assert spec is not None and spec.loader is not None
    module = module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def test_offline_synthetic_operator_self_test_covers_even_and_odd_shapes():
    audit = load_audit_module()
    result = audit.synthetic_operator_self_test(seed=1729)
    assert result["synthetic_only"] is True
    assert result["real_psf_receipt"] is False
    assert result["shapes_checked"] >= 4
    assert result["max_fft_vs_roll_abs_error"] < 1e-12
    assert result["gershgorin_supports_checked"] > 0
    assert result["gershgorin_bound_violations"] == 0


def test_self_test_does_not_promote_real_data_certificate():
    audit = load_audit_module()
    result = audit.synthetic_operator_self_test(seed=17)
    assert result["source_operator_identity_tested"] is True
    assert result["sparse_bound_compiler_tested"] is True
    assert result["real_psf_receipt"] is False
    assert result["physical_photon_calibration"] is False
