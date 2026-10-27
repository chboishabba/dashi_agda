"""Synthetic self-test for the calibrated ARPES observer builder.

No Igor/source data are used. This checks deterministic axis/channel assembly and
uncertainty handling only and makes no Co1/4TaSe2 observation claim.
"""
from __future__ import annotations

import json
import numpy as np

from co_tase2_arpes_observer_from_ibw import assemble_observer


def run():
    energy = np.linspace(-0.2, 0.1, 7)
    momentum = np.linspace(-0.1, 0.1, 5)
    up = np.arange(35, dtype=float).reshape(5, 7) + 20.0
    dn = up[::-1].copy() + 3.0
    out = assemble_observer(
        arrays=[up, dn],
        energy_axes=[energy, energy.copy()],
        momentum_axes=[momentum, momentum.copy()],
        sigmas=[np.sqrt(up), np.sqrt(dn)],
        source_digests=["a" * 64, "b" * 64],
        photon_energy_ev=55.0,
        temperature_k=7.0,
        polarimeter_response_model="synthetic calibrated identity",
        spin_channels_calibrated=True,
    )
    assert out["intensity"].shape == (2, 5, 7)
    assert out["sigma_intensity"].shape == out["intensity"].shape
    assert np.allclose(out["energy_ev"], energy)
    assert np.allclose(out["momentum_inv_a"], momentum)
    assert len(out["source_sha256"]) == 64
    return {
        "status": "PASS",
        "scope": "synthetic observer assembly only",
        "material_claim": False,
    }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
