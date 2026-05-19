import math
import importlib.util
from pathlib import Path


SCRIPT = Path(__file__).resolve().parents[1] / "scripts" / "run_w4w5_ct18_corrected_dy_luminosity.py"
SPEC = importlib.util.spec_from_file_location("run_w4w5_ct18_corrected_dy_luminosity", SCRIPT)
assert SPEC is not None
MODULE = importlib.util.module_from_spec(SPEC)
assert SPEC.loader is not None
SPEC.loader.exec_module(MODULE)
dy_dluminosity_dtau = MODULE.dy_dluminosity_dtau


class ConstantFlavorPDF:
    values = {
        2: 3.0,
        -2: 5.0,
        1: 7.0,
        -1: 11.0,
        3: 13.0,
        -3: 17.0,
    }

    def xfxQ(self, pid, x, q):
        return x * self.values[pid]


def test_dy_dluminosity_dtau_uses_full_dx_over_x_convention():
    pdf = ConstantFlavorPDF()
    mass = 100.0
    sqrt_s = 1000.0
    tau = (mass / sqrt_s) ** 2
    charge_weighted_constant = (4.0 / 9.0) * (30.0) + (1.0 / 9.0) * (154.0) + (
        1.0 / 9.0
    ) * (442.0)

    observed = dy_dluminosity_dtau(pdf, mass, sqrt_s=sqrt_s, n_x=1001)

    assert math.isclose(
        observed,
        charge_weighted_constant * math.log(0.999999 / tau),
        rel_tol=1.0e-12,
    )
