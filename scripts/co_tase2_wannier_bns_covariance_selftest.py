"""Synthetic self-test for the material-basis BNS covariance auditor.

The fixture uses a real diagonal two-orbital onsite Hamiltonian and identity
sewing matrices at Gamma for every literal BNS operation. It tests audit
mechanics/authority coverage only and carries no Co1/4TaSe2 material claim.
"""
from __future__ import annotations

import json
import tempfile
from pathlib import Path

import numpy as np

from co_tase2_wannier_bns_covariance_audit import audit


def run():
    root = Path(__file__).resolve().parents[1]
    authority = root / "data/co_tase2/bns_194_268_magndata_operations.json"
    ops = json.loads(authority.read_text())["operations"]
    with tempfile.TemporaryDirectory() as td:
        td = Path(td)
        hr = td / "toy_hr.dat"
        samples = td / "samples.npz"
        hr.write_text(
            "synthetic covariance fixture\n2\n1\n1\n"
            "0 0 0 1 1 -0.1 0\n"
            "0 0 0 1 2 0 0\n"
            "0 0 0 2 1 0 0\n"
            "0 0 0 2 2 0.1 0\n"
        )
        n = len(ops)
        sewing = np.repeat(np.eye(2, dtype=complex)[None, :, :], n, axis=0)
        zero = np.zeros((n, 3), float)
        np.savez_compressed(
            samples,
            operation_triplet=np.asarray([x["triplet"] for x in ops]),
            antiunitary=np.asarray([x["antiunitary"] for x in ops], bool),
            k_fractional=zero,
            transformed_k_fractional=zero,
            sewing=sewing,
            source_identity=np.asarray("synthetic covariance self-test"),
        )
        result = audit(hr, authority, samples)
        assert result["authority_operations"] == 24
        assert result["covered_operations"] == 24
        assert result["samples"] == 24
        assert result["max_unitarity_defect"] < 1e-12
        assert result["max_covariance_defect"] < 1e-12
        return {
            "status": "PASS",
            "scope": "synthetic material-basis covariance audit mechanics only",
            "material_claim": False,
        }


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
