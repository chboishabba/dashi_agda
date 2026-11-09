#!/usr/bin/env python3
"""Fail-closed source adapter: acquired Rhea 29x12 -> candidate 369 reactive PNP.

The Rhea certificate establishes stoichiometry/identity, NOT measured kinetics.
This adapter requires a separate complete, provenance-labelled physical parameter
manifest for one explicitly selected specimen, time and compartment. It only
supports the existing closed-mass, blocking boundary/grounded-potential solver.
No automatic source trust, physiological calibration, or Golden proof promotion.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import math
from pathlib import Path
import sys

import numpy as np

from check_bh4_original_panel_spatial_events import (
    check_certificate, load_original_receipt_json,
)
from reactive_pnp_369 import Model

_REQUIRED_PHYSICS = ("epsilon", "RT", "F", "h")
_ALLOWED_BOUNDARY = {
    "mass": "blocking",
    "potential": "dirichlet_zero_all_six_faces",
    "electrode": "none",
}
_REQUIRED_CONTEXT = ("specimen_id", "measurement_time", "compartment",
                     "source_reference", "parameter_source_reference")


def _exact_keys(mapping, keys, label):
    if not isinstance(mapping, dict) or set(mapping) != set(keys):
        raise ValueError(f"{label} requires exact original keys; no missing/extra entries")


def _finite_number(value, label, *, positive=False, nonnegative=False):
    if isinstance(value, bool) or not isinstance(value, (int, float)):
        raise ValueError(f"{label}: numeric value required")
    number = float(value)
    if not math.isfinite(number):
        raise ValueError(f"{label}: nonfinite numeric value")
    if positive and not number > 0:
        raise ValueError(f"{label}: strictly positive value required")
    if nonnegative and number < 0:
        raise ValueError(f"{label}: nonnegative value required")
    return number


def _source_ref(entry, label):
    if not isinstance(entry, dict) or not isinstance(entry.get("source_reference"), str):
        raise ValueError(f"{label}: individual source reference required")
    if not entry["source_reference"].strip():
        raise ValueError(f"{label}: blank source reference")
    # Syntactic provenance is not independent authentication.
    return entry["source_reference"]


def make_candidate(source_bytes: bytes, manifest: dict, *, pinned_sha256: str):
    """Return (Model, conservative candidate-only receipt).

    Full original Rhea matrix and participant formula/charge verification is
    delegated to the existing original-panel checker, never reimplemented.
    """
    if not isinstance(source_bytes, bytes):
        raise ValueError("original source bytes required")
    source_sha = hashlib.sha256(source_bytes).hexdigest()
    if not isinstance(pinned_sha256, str) or len(pinned_sha256) != 64:
        raise ValueError("64-character pinned source SHA-256 required")
    if source_sha != pinned_sha256.lower():
        raise ValueError("original Rhea source digest mismatch")
    certificate = load_original_receipt_json(source_bytes.decode("utf-8"))
    matrix, by_species = check_certificate(certificate, full_panel=True)
    species = matrix["species_index"]
    reactions = matrix["reaction_index"]
    S = np.asarray(matrix["matrix"], dtype=np.int64)
    if S.shape != (29, 12):
        raise ValueError("original 29x12 finite matrix required")
    if not isinstance(manifest, dict):
        raise ValueError("parameter manifest required")
    for field in _REQUIRED_CONTEXT:
        if not isinstance(manifest.get(field), str) or not manifest[field].strip():
            raise ValueError(f"missing source-scoped {field}")
    if manifest.get("source_sha256") != source_sha:
        raise ValueError("manifest must bind to exact original Rhea source")
    if manifest.get("boundary") != _ALLOWED_BOUNDARY:
        raise ValueError("unsupported/open/reactive boundary: no hidden exchange")
    if manifest.get("external_exchange") != []:
        raise ValueError("external exchange unsupported in this closed-mass solver")
    compartments = manifest.get("voxel_compartments")
    if not isinstance(compartments, list) or len(compartments) != 27:
        raise ValueError("27 explicit native voxel compartments required")
    if any(x != manifest["compartment"] for x in compartments):
        raise ValueError("multicompartment transport needs original interface laws")

    param_species = manifest.get("species")
    param_reactions = manifest.get("reactions")
    _exact_keys(param_species, species, "source species")
    _exact_keys(param_reactions, reactions, "source reaction columns")
    physics = manifest.get("physics")
    _exact_keys(physics, (*_REQUIRED_PHYSICS, "fixed_charge"), "physical parameters")
    for name in _REQUIRED_PHYSICS:
        _source_ref(physics[name], name)
    z, D, standard_mu = [], [], []
    for key in species:
        entry = param_species[key]
        _source_ref(entry, f"species {key}")
        _exact_keys(entry, ("charge", "D", "standard_mu", "source_reference"), key)
        charge = _finite_number(entry["charge"], f"{key} charge")
        if charge != by_species[key][1]:
            raise ValueError(f"{key}: valence contradicts original Rhea charge")
        z.append(charge)
        D.append(_finite_number(entry["D"], f"{key} diffusion", nonnegative=True))
        standard_mu.append(_finite_number(entry["standard_mu"], f"{key} chemical potential"))
    kf, kb = [], []
    for key in reactions:
        entry = param_reactions[key]
        _source_ref(entry, f"reaction {key}")
        _exact_keys(entry, ("kf", "kb", "source_reference"), key)
        kf.append(_finite_number(entry["kf"], f"{key} kf", positive=True))
        kb.append(_finite_number(entry["kb"], f"{key} kb", positive=True))
    physics_values = {}
    for key, entry in physics.items():
        _source_ref(entry, key)
        _exact_keys(entry, ("value", "source_reference"), key)
        physics_values[key] = _finite_number(
            entry["value"], key, positive=key != "fixed_charge")
    # Every finite reaction column has canonical consumed/produced counts.
    reactants = np.maximum(-S.T, 0)
    products = np.maximum(S.T, 0)
    if not np.array_equal(products - reactants, S.T):
        raise AssertionError("original signed matrix orientation failure")
    model = Model(
        z=np.asarray(z, dtype=float), D=np.asarray(D, dtype=float),
        reactants=reactants, products=products,
        kf=np.asarray(kf, dtype=float), kb=np.asarray(kb, dtype=float),
        standard_mu=np.asarray(standard_mu, dtype=float),
        **physics_values,
    )
    return model, {
        "kind": "dashi.bh4.original-reactive-pnp-candidate.v1",
        "source_sha256": source_sha,
        "species_count": len(species),
        "reaction_count": len(reactions),
        "voxel_count": 27,
        "native_bond_count": 54,
        "source_specimen": manifest["specimen_id"],
        "measurement_time": manifest["measurement_time"],
        "compartment": manifest["compartment"],
        "boundary": manifest["boundary"],
        "original_reaction_columns": list(reactions),
        "source_reaction_identity_checked": True,
        "source_reaction_atom_charge_balanced": True,
        "parameter_source_references_present": True,
        "parameter_sources_independently_authenticated": False,
        "original_rates_independently_measured": False,
        "physical_observer_commutation_proven": False,
        "original_closed_system_candidate_only": True,
        "physiological_or_clinical_validation": False,
        "agda_kernel_checked": False,
    }


def main(argv=None):
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--source", type=Path, required=True)
    parser.add_argument("--manifest", type=Path, required=True)
    parser.add_argument("--source-sha256", required=True)
    parser.add_argument("--receipt", type=Path, required=True)
    args = parser.parse_args(argv)
    source_bytes = args.source.read_bytes()
    manifest = load_original_receipt_json(args.manifest.read_text(encoding="utf-8"))
    _, receipt = make_candidate(
        source_bytes, manifest, pinned_sha256=args.source_sha256)
    args.receipt.write_text(
        json.dumps(receipt, sort_keys=True, indent=2) + "\n", encoding="utf-8")
    print("candidate-only source-gated PNP model validated; no physical promotion")
    return 0


if __name__ == "__main__":
    sys.exit(main())
