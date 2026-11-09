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
from reactive_pnp_369 import Model, implicit_step
from build_bh4_stoichiometric_matrix import participant_key

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
    # Mass-action orders require original gross sides, not net S:
    # unchanged catalysts may occur on BOTH sides of a Rhea equation.
    reactants = np.zeros((12, 29), dtype=np.int64)
    products = np.zeros((12, 29), dtype=np.int64)
    species_pos = {key: i for i, key in enumerate(species)}
    reaction_pos = {key: j for j, key in enumerate(reactions)}
    seen_reactions = set()
    for row in certificate["reactions"]:
        if not row.get("formula_charge_ready"):
            continue
        rid = str(row.get("rhea_id", ""))
        if rid not in reaction_pos or rid in seen_reactions:
            raise ValueError("unmatched or duplicated original reaction")
        seen_reactions.add(rid)
        j = reaction_pos[rid]
        for participant in row["participants"]:
            key = participant_key(participant)
            if key not in species_pos:
                raise ValueError("unmatched original reaction participant")
            coeff = int(str(participant.get("coefficient", 1)))
            if coeff <= 0:
                raise ValueError("nonpositive original reaction stoichiometry")
            if participant.get("side") == "substrate":
                reactants[j, species_pos[key]] += coeff
            elif participant.get("side") == "product":
                products[j, species_pos[key]] += coeff
            else:
                raise ValueError("untyped original reaction side")
    if seen_reactions != set(reactions):
        raise ValueError("original 12 reaction identities incomplete")
    if not np.array_equal(products - reactants, S.T):
        raise ValueError("original source participants disagree with signed S")
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


def check_original_closed_inventory(
    source_bytes: bytes, pinned_sha256: str,
    before: np.ndarray, after: np.ndarray, *, atol: float = 1e-8,
):
    """Numerically audit original Rhea CHNOP/charge inventory after a step.

    Checks the real original-panel certificate again; a candidate time step
    cannot inherit atom/charge validity from synthetically named species.
    Finite floating-point tolerance is an audit, not an Agda equality proof.
    """
    if not isinstance(source_bytes, bytes):
        raise ValueError("original source bytes required")
    digest = hashlib.sha256(source_bytes).hexdigest()
    if not isinstance(pinned_sha256, str) or digest != pinned_sha256.lower():
        raise ValueError("original source digest mismatch")
    if not isinstance(atol, (int, float)) or isinstance(atol, bool):
        raise ValueError("finite nonnegative audit tolerance required")
    if not math.isfinite(float(atol)) or atol < 0:
        raise ValueError("finite nonnegative audit tolerance required")
    certificate = load_original_receipt_json(source_bytes.decode("utf-8"))
    matrix, by_species = check_certificate(certificate, full_panel=True)
    species = matrix["species_index"]
    a = np.asarray(before, dtype=float)
    b = np.asarray(after, dtype=float)
    if a.shape != (27, len(species)) or b.shape != a.shape:
        raise ValueError("same complete original 27x29 concentration chart required")
    if not np.all(np.isfinite(a)) or not np.all(np.isfinite(b)):
        raise ValueError("nonfinite original state concentrations")
    if np.any(a < 0) or np.any(b < 0):
        raise ValueError("negative original source concentration")
    elements = ("C", "H", "N", "O", "P")
    atom_matrix = np.asarray([
        [by_species[key][0].get(el, 0) for el in elements]
        for key in species
    ], dtype=float)
    charge = np.asarray([by_species[key][1] for key in species], dtype=float)
    if np.any(~np.isfinite(atom_matrix)) or not np.all(np.isfinite(charge)):
        raise ValueError("invalid original molecular formula or charge")
    # Rates are concentration per volume. Uniform h^3 cancels from the
    # equality comparison; this checks relative inventory, not mole amounts.
    delta = np.sum(b - a, axis=0)
    atom_defect = delta @ atom_matrix
    charge_defect = float(delta @ charge)
    max_defect = max(float(np.max(np.abs(atom_defect))), abs(charge_defect))
    if max_defect > float(atol):
        raise ValueError("source-specific closed CHNOP/charge audit failed")
    return {
        "source_sha256": digest,
        "original_species_count": len(species),
        "voxel_count": 27,
        "atom_inventory_defect": dict(zip(elements, map(float, atom_defect))),
        "charge_inventory_defect": charge_defect,
        "max_inventory_defect": max_defect,
        "numerical_tolerance": float(atol),
        "numerical_candidate_only": True,
        "agda_kernel_checked": False,
        "independent_source_authenticated": False,
    }


def source_bound_closed_implicit_step(
    source_bytes: bytes, manifest: dict, *, pinned_sha256: str,
    initial_concentrations: np.ndarray, dt: float,
    residual_tolerance: float = 1e-8,
    inventory_tolerance: float = 1e-7,
):
    """Run ONE original-certificate-bound numerical PNP candidate step.

    No empirical promotion: model inputs still require independent
    source authentication, and root convergence is not analytic existence.
    The source certificate, 27x29 before/after pair, solver and atomic
    inventory audit all refer to this one selected candidate step.
    """
    model, source_receipt = make_candidate(
        source_bytes, manifest, pinned_sha256=pinned_sha256)
    before = np.asarray(initial_concentrations, dtype=float)
    if before.shape != (27, 29) or not np.all(np.isfinite(before)):
        raise ValueError("one complete finite 27x29 original physical initial state required")
    if np.any(before <= 0):
        raise ValueError("existing logarithmic implicit solver requires positive initial concentrations")
    residual_tolerance = _finite_number(
        residual_tolerance, "residual tolerance", positive=True)
    inventory_tolerance = _finite_number(
        inventory_tolerance, "inventory tolerance", nonnegative=True)
    dt = _finite_number(dt, "physical timestep", positive=True)
    # A separate synthetic solver with the right number of variables is
    # not substituted: this is the selected native 369 PNP operator.
    after, numerical = implicit_step(
        before, dt, model, rtol=residual_tolerance)
    inventory = check_original_closed_inventory(
        source_bytes, pinned_sha256, before, after,
        atol=inventory_tolerance)
    if not (isinstance(numerical, dict)
            and numerical.get("numerical_residual_max", float("inf"))
                <= residual_tolerance):
        raise ValueError("same-step original PNP residual receipt missing or invalid")
    if numerical.get("free_energy_after", float("inf")) > (
        numerical.get("free_energy_before", float("-inf"))
        + max(1e-9, residual_tolerance *
              max(1.0, abs(numerical.get("free_energy_before", 0.0))))
    ):
        raise ValueError("same-step original PNP energy receipt invalid")
    # Re-audit the candidate output shape and physical domain before any
    # receipt: do not let an arbitrary test double supply a malformed state.
    after = np.asarray(after, dtype=float)
    if after.shape != before.shape or not np.all(np.isfinite(after)) or np.any(after <= 0):
        raise ValueError("same-step PNP output state invalid")
    return after, {
        "kind": "dashi.bh4.original-closed-pnp-step-candidate.v1",
        "source_receipt": source_receipt,
        "solver_diagnostics": numerical,
        "source_inventory_audit": inventory,
        "initial_state_shape": [27, 29],
        "physical_dt": dt,
        "source_bound_same_step": True,
        "candidate_only": True,
        "physical_one_step_agda_proven": False,
        "original_parameters_independently_authenticated": False,
        "independent_longitudinal_validation": False,
        "agda_kernel_checked": False,
    }
