"""Synthetic format self-test for co_tase2_wannier90_spectral.py.

This exercises parser/interpolation/schema mechanics only.  The fixture is a
2-orbital onsite Hamiltonian and MUST NOT be interpreted as Co1/4TaSe2 physics.
"""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

import numpy as np

from co_tase2_wannier90_spectral import produce


def run():
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        hr = td / "toy_hr.dat"
        meta = td / "meta.json"
        path = td / "path.json"
        out = td / "spectral.npz"
        receipt = td / "receipt.json"

        # one R point, two Wannier functions, complete 2x2 matrix
        hr.write_text(
            "synthetic format-only fixture\n"
            "2\n"
            "1\n"
            "1\n"
            "0 0 0 1 1 -0.10 0.0\n"
            "0 0 0 1 2  0.00 0.0\n"
            "0 0 0 2 1  0.00 0.0\n"
            "0 0 0 2 2  0.10 0.0\n"
        )
        meta.write_text(json.dumps({
            "soc_included": True,
            "exchange_included": True,
            "spin_basis_model": "synthetic up/down diagonal basis",
            "spin_projectors": [[1.0, 0.0], [0.0, 1.0]],
            "reciprocal_cartesian_inv_a": [
                [1.0, 0.0, 0.0],
                [0.0, 1.0, 0.0],
                [0.0, 0.0, 1.0],
            ],
            "fermi_energy_ev": 0.0,
            "temperature_k": 7.0,
            "broadening_ev": 0.01,
            "energy_min_ev": -0.3,
            "energy_max_ev": 0.3,
            "energy_points": 121,
            "matrix_element_model": "identity-format-selftest",
            "kz_broadening_model": "none-format-selftest",
            "source_identity": "synthetic-format-selftest",
        }))
        path.write_text(json.dumps({
            "k_fractional": [[0, 0, 0], [0.5, 0, 0], [1.0, 0, 0]]
        }))

        r = produce(hr, meta, path, out, receipt)
        with np.load(out, allow_pickle=False) as d:
            assert d["spectral"].shape == (2, 3, 121)
            assert np.all(np.diff(d["energy_ev"]) > 0)
            assert np.all(np.diff(d["momentum_inv_a"]) > 0)
            assert bool(d["soc_included"].item())
            assert bool(d["exchange_included"].item())
            # onsite-only H is k independent, so each channel spectrum repeats.
            assert np.allclose(d["spectral"][:, 0], d["spectral"][:, 1])
            assert np.allclose(d["spectral"][:, 1], d["spectral"][:, 2])
        assert r["num_wann"] == 2
        assert r["nrpts"] == 1
        assert r["spin_channels"] == 2
        assert r["max_hermiticity_defect"] == 0.0
        return {
            "status": "PASS",
            "scope": "synthetic format/interpolation/schema self-test only",
            "material_claim": False,
            "num_wann": 2,
            "spin_channels": 2,
        }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
