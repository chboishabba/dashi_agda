"""Validate publication-level Co1/4TaSe2 ARPES constraints.

This script intentionally does NOT fit raw data and does NOT digitise figures.
It pins the numerical/qualitative constraints explicitly stated in the paper so
future material Hamiltonians and raw-data observers have a same-object target.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path


def load_constraints(path: str | Path):
    path = Path(path)
    raw = path.read_bytes()
    data = json.loads(raw)
    return path, raw, data


def validate(path: str | Path):
    path, raw, d = load_constraints(path)
    if d.get("source_doi") != "10.1038/s41467-026-76784-x":
        raise ValueError("unexpected source DOI")

    low = int(d["sample_temperature_low_K"])
    high = int(d["sample_temperature_high_K"])
    tn = int(d["neel_temperature_K"])
    if not (low < tn < high):
        raise AssertionError((low, tn, high))

    photons = {int(x["photon_energy_eV"]): x for x in d["photon_conditions"]}
    for required in (48, 51, 55):
        if required not in photons:
            raise AssertionError(f"missing photon condition {required} eV")
    if photons[55]["assigned_kz"] != "approximately pi/(2c)":
        raise AssertionError("55 eV kz assignment drifted")
    if photons[48]["assigned_kz"] != "approximately 0":
        raise AssertionError("48 eV kz assignment drifted")
    if "two" not in photons[55]["published_lineshape"]:
        raise AssertionError("55 eV must retain the published two-feature/two-peak target")
    if photons[48]["published_lineshape"] != "single-peak":
        raise AssertionError("48 eV must retain the published single-peak target")

    p = d["published_momentum_constraints"]
    dft_sep = float(p["dft_fermi_crossing_separation_inverse_A"])
    mdc_sep = float(p["voigt_fit_peak_separation_inverse_A"])
    inst_width = float(p["instrumental_gaussian_peak_width_inverse_A"])
    if (dft_sep, mdc_sep, inst_width) != (0.01, 0.09, 0.08):
        raise AssertionError("published momentum targets drifted")
    # The publication itself says the fitted separation is close to the
    # instrumental Gaussian width.  Record the ratio but do not turn this into
    # an unreported significance test.
    ratio = mdc_sep / inst_width

    direction = d["directional_constraints"]
    if "spin-degenerate" not in direction["GammaPrime_KPrime"]:
        raise AssertionError("Gamma'-K' nodal target missing")
    if "spin-split" not in direction["GammaPrime_MPrime"]:
        raise AssertionError("Gamma'-M' split target missing")

    return {
        "input_sha256": hashlib.sha256(raw).hexdigest(),
        "source_doi": d["source_doi"],
        "temperature_ordering_low_lt_TN_lt_high": True,
        "published_photon_conditions_pinned": True,
        "published_directional_constraints_pinned": True,
        "dft_crossing_separation_inverse_A": dft_sep,
        "voigt_fit_peak_separation_inverse_A": mdc_sep,
        "instrumental_gaussian_width_inverse_A": inst_width,
        "fit_separation_to_instrument_width_ratio": ratio,
        "raw_igor_payload_consumed": False,
        "pixel_digitisation_used": False,
        "material_hamiltonian_fit_closed": False,
        "status": "publication-summary target paid; raw-data/material-H same-object fit remains open",
    }


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("constraints", nargs="?", default="data/co_tase2/published_arpes_constraints_2026.json")
    p.add_argument("--receipt")
    args = p.parse_args()
    receipt = validate(args.constraints)
    if args.receipt:
        Path(args.receipt).write_text(json.dumps(receipt, indent=2) + "\n")
    print(json.dumps(receipt, indent=2))
