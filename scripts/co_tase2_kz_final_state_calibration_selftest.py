"""Synthetic self-test for the ARPES free-electron final-state kz consumer.

This tests arithmetic/folding only. The parameters are deliberately synthetic
and make no Co1/4TaSe2 calibration claim.
"""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

from co_tase2_kz_final_state_calibration import evaluate, kz_inverse_a


def run():
    with tempfile.TemporaryDirectory() as td:
        p = Path(td) / "synthetic.json"
        # Pick finite physically plausible values solely to exercise the model.
        cfg = {
            "work_function_ev": 4.5,
            "inner_potential_ev": 12.0,
            "c_angstrom": 12.0,
            "calibration_model": "synthetic free-electron final-state self-test",
            "parameter_source": "synthetic self-test; not material data",
            "points": [
                {"label": "p0", "photon_energy_ev": 48.0, "binding_energy_ev": 0.0, "theta_deg": 0.0},
                {"label": "p1", "photon_energy_ev": 55.0, "binding_energy_ev": 0.0, "theta_deg": 10.0},
            ],
        }
        p.write_text(json.dumps(cfg))
        out = evaluate(p)
        assert len(out["points"]) == 2
        for row in out["points"]:
            assert row["kz_absolute_inv_a"] > 0
            assert 0 <= row["kz_folded_fraction_of_2pi_over_c"] < 1
        assert kz_inverse_a(55.0, 4.5, 0.0, 0.0, 12.0) > kz_inverse_a(48.0, 4.5, 0.0, 0.0, 12.0)
        return {
            "status": "PASS",
            "scope": "synthetic final-state calibration arithmetic/folding only",
            "material_claim": False,
        }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
