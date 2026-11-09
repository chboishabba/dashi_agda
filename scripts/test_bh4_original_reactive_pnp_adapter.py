"""Fail-closed adapter regressions. All example data are SYNTHETIC.

The monkeypatched original-panel checker is used only to exercise parameter
validation without misrepresenting any synthetic rows as acquired Rhea.
A positive real-source run still requires check_certificate(full_panel=True).
"""
from copy import deepcopy
import hashlib
import json

import numpy as np
import pytest

import bh4_original_reactive_pnp_adapter as Adapter


def fixture(monkeypatch):
    source = b'{"schema":"synthetic-only"}'
    sha = hashlib.sha256(source).hexdigest()
    species = [f"synthetic-S{i:02d}" for i in range(29)]
    reactions = [f"synthetic-R{i:02d}" for i in range(12)]
    S = [[0 for _ in reactions] for _ in species]
    rows = []
    for j, rid in enumerate(reactions):
        S[j][j] = -1
        S[j+12][j] = 1
        rows.append({"rhea_id": rid, "formula_charge_ready": True, "participants": [
            {"side": "substrate", "chebi_id": species[j], "coefficient": 1},
            {"side": "product", "chebi_id": species[j+12], "coefficient": 1},
        ]})
    certificate = {"reactions": rows}
    matrix = {"species_index": species, "reaction_index": reactions, "matrix": S}
    by_species = {s: ({}, 0) for s in species}
    monkeypatch.setattr(Adapter, "load_original_receipt_json", lambda _: certificate)
    monkeypatch.setattr(Adapter, "check_certificate", lambda *a, **kw: (matrix, by_species))
    param = {"source_sha256": sha, "specimen_id": "synthetic-specimen",
        "measurement_time": "synthetic-time", "compartment": "synthetic-cytosol",
        "source_reference": "synthetic-source", "parameter_source_reference": "synthetic-parameters",
        "boundary": {"mass": "blocking", "potential": "dirichlet_zero_all_six_faces",
                     "electrode": "none"}, "external_exchange": [],
        "voxel_compartments": ["synthetic-cytosol"]*27,
        "species": {s: {"charge": 0, "D": 0.1, "standard_mu": 0.0,
                         "source_reference": "synthetic-param"} for s in species},
        "reactions": {r: {"kf": 0.05, "kb": 0.05,
                          "source_reference": "synthetic-rate"} for r in reactions},
        "physics": {k: {"value": v, "source_reference": "synthetic-physics"}
                    for k,v in {"epsilon": 1.0, "RT": 1.0, "F": 1.0,
                                "h": 1.0, "fixed_charge": 0.0}.items()},
    }
    return source, sha, param, species, reactions


def test_synthetic_shape_and_no_promotion(monkeypatch):
    source, sha, param, species, reactions = fixture(monkeypatch)
    model, receipt = Adapter.make_candidate(source, param, pinned_sha256=sha)
    assert model.reactants.shape == (12,29)
    assert model.products.shape == (12,29)
    assert receipt["native_bond_count"] == 54
    assert receipt["original_closed_system_candidate_only"]
    assert not receipt["parameter_sources_independently_authenticated"]
    assert not receipt["agda_kernel_checked"]


def test_source_digest_and_missing_parameter_fail_closed(monkeypatch):
    source, sha, param, species, reactions = fixture(monkeypatch)
    with pytest.raises(ValueError):
        Adapter.make_candidate(source, param, pinned_sha256="0"*64)
    q = deepcopy(param); del q["species"][species[0]]
    with pytest.raises(ValueError):
        Adapter.make_candidate(source, q, pinned_sha256=sha)
    q = deepcopy(param); q["reactions"][reactions[0]]["source_reference"] = ""
    with pytest.raises(ValueError):
        Adapter.make_candidate(source, q, pinned_sha256=sha)


def test_no_imputed_physical_exchange_or_compartment(monkeypatch):
    source, sha, param, species, reactions = fixture(monkeypatch)
    for key, replacement in [
        ("external_exchange", [{"species": species[0]}]),
        ("voxel_compartments", ["other"] + ["synthetic-cytosol"]*26),
        ("boundary", {"mass": "reactive", "potential": "dirichlet_zero_all_six_faces",
                      "electrode": "none"}),
    ]:
        q = deepcopy(param); q[key] = replacement
        with pytest.raises(ValueError):
            Adapter.make_candidate(source, q, pinned_sha256=sha)


def test_source_valence_and_thermodynamics_fail_closed(monkeypatch):
    source, sha, param, species, reactions = fixture(monkeypatch)
    q = deepcopy(param); q["species"][species[0]]["charge"] = 1
    with pytest.raises(ValueError):
        Adapter.make_candidate(source, q, pinned_sha256=sha)
    q = deepcopy(param); q["reactions"][reactions[0]]["kf"] = 0.1
    with pytest.raises((AssertionError, ValueError)):
        Adapter.make_candidate(source, q, pinned_sha256=sha)
    q = deepcopy(param); q["physics"]["RT"]["value"] = float("nan")
    with pytest.raises(ValueError):
        Adapter.make_candidate(source, q, pinned_sha256=sha)


def test_original_gross_catalyst_orders_are_retained(monkeypatch):
    source, sha, param, species, reactions = fixture(monkeypatch)
    original_loader = Adapter.load_original_receipt_json
    certificate = original_loader(source)
    certificate["reactions"][0]["participants"] += [
        {"side": "substrate", "chebi_id": species[28], "coefficient": 1},
        {"side": "product", "chebi_id": species[28], "coefficient": 1},
    ]
    monkeypatch.setattr(Adapter, "load_original_receipt_json", lambda _: certificate)
    model, receipt = Adapter.make_candidate(source, param, pinned_sha256=sha)
    assert model.reactants[0,28] == 1
    assert model.products[0,28] == 1
    assert model.reactants[0,0] == 1
    assert model.products[0,12] == 1


def test_original_source_specific_closed_inventory_audit(monkeypatch):
    source, sha, manifest, species, reactions = fixture(monkeypatch)
    certificate = Adapter.load_original_receipt_json(source)
    matrix, _ = Adapter.check_certificate(certificate, full_panel=True)
    paid_formula = {s: ({"C": 1}, 0) for s in species}
    paid_formula[species[0]] = ({"C": 2, "H": 1}, 1)
    paid_formula[species[1]] = ({"C": 2, "H": 1}, 1)
    monkeypatch.setattr(Adapter, "check_certificate",
                        lambda *a, **kw: (matrix, paid_formula))
    before = np.ones((27,29))
    after = before.copy()
    after[0,0] -= 0.25
    after[1,0] += 0.25
    result = Adapter.check_original_closed_inventory(
        source, sha, before, after)
    assert result["max_inventory_defect"] < 1e-12
    assert not result["agda_kernel_checked"]
    assert not result["independent_source_authenticated"]
    after[2,0] += 0.5
    with pytest.raises(ValueError, match="inventory"):
        Adapter.check_original_closed_inventory(
            source, sha, before, after)
    with pytest.raises(ValueError, match="digest"):
        Adapter.check_original_closed_inventory(
            source, "0"*64, before, before)


def test_original_inventory_negative_nonfinite_and_shape(monkeypatch):
    source, sha, manifest, species, reactions = fixture(monkeypatch)
    a = np.ones((27,29))
    q = a.copy()
    q[0,0] = -1
    with pytest.raises(ValueError):
        Adapter.check_original_closed_inventory(source,sha,a,q)
    q = a.copy()
    q[0,0] = float("nan")
    with pytest.raises(ValueError):
        Adapter.check_original_closed_inventory(source,sha,a,q)
    with pytest.raises(ValueError):
        Adapter.check_original_closed_inventory(source,sha,a,a[:26])
    with pytest.raises(ValueError):
        Adapter.check_original_closed_inventory(source,sha,a,a,atol=float("inf"))


def test_source_bound_one_step_same_state_candidate(monkeypatch):
    source, sha, manifest, species, reactions = fixture(monkeypatch)
    before = np.ones((27,29))
    called = []
    def synthetic_solver(c, dt, model, rtol):
        called.append((dt, c.shape, model.reactants.shape, rtol))
        return c.copy(), {
            "numerical_residual_max": 0.0,
            "free_energy_before": 0.0,
            "free_energy_after": 0.0,
            "charge_defect": 0.0,
            "minimum_concentration": 1.0,
            "poisson_residual_max": 0.0,
            "transport_power": 0.0,
            "reaction_power": 0.0,
        }
    monkeypatch.setattr(Adapter, "implicit_step", synthetic_solver)
    after, receipt = Adapter.source_bound_closed_implicit_step(
        source, manifest, pinned_sha256=sha,
        initial_concentrations=before, dt=0.01)
    assert np.array_equal(after, before)
    assert called == [(0.01, (27,29), (12,29), 1e-8)]
    assert receipt["source_bound_same_step"]
    assert receipt["source_inventory_audit"]["max_inventory_defect"] == 0.0
    assert not receipt["physical_one_step_agda_proven"]
    assert not receipt["original_parameters_independently_authenticated"]


def test_same_step_receipt_rejects_nonfinite_or_missing_diagnostics(monkeypatch):
    source, sha, manifest, species, reactions = fixture(monkeypatch)
    before = np.ones((27,29))
    good = {
        "numerical_residual_max": 0.0,
        "free_energy_before": 0.0,
        "free_energy_after": 0.0,
        "charge_defect": 0.0,
        "minimum_concentration": 1.0,
        "poisson_residual_max": 0.0,
        "transport_power": 0.0,
        "reaction_power": 0.0,
    }
    for key, value in (
        ("free_energy_after", float("nan")),
        ("numerical_residual_max", float("nan")),
        ("transport_power", float("inf")),
        ("poisson_residual_max", 0.1),
        ("reaction_power", 0.01),
        ("minimum_concentration", -1.0),
    ):
        diagnostics = dict(good); diagnostics[key] = value
        monkeypatch.setattr(Adapter, "implicit_step",
                            lambda *a, **k: (before.copy(), diagnostics))
        with pytest.raises(ValueError):
            Adapter.source_bound_closed_implicit_step(
                source, manifest, pinned_sha256=sha,
                initial_concentrations=before, dt=0.01)
    diagnostics = dict(good); del diagnostics["charge_defect"]
    monkeypatch.setattr(Adapter, "implicit_step",
                        lambda *a, **k: (before.copy(), diagnostics))
    with pytest.raises(ValueError):
        Adapter.source_bound_closed_implicit_step(
            source, manifest, pinned_sha256=sha,
            initial_concentrations=before, dt=0.01)


def test_original_formula_weighted_brouwer_contract(monkeypatch):
    source,sha,manifest,species,reactions=fixture(monkeypatch)
    certificate=Adapter.load_original_receipt_json(source)
    matrix,_=Adapter.check_certificate(certificate,full_panel=True)
    paid={s:({"C":1},0) for s in species}
    monkeypatch.setattr(Adapter,"check_certificate",
                        lambda *args,**kw: (matrix,paid))
    receipt=Adapter.source_bound_closed_brouwer_existence(
        source,manifest,pinned_sha256=sha,
        initial_concentrations=np.ones((27,29)),dt=2.0)
    assert receipt["exact_integer_source_weighted_reactions_verified"]
    assert len(receipt["conserved_original_CHNOP_weights"])==29
    theorem=receipt["mathematical_root_existence_contract"]
    assert theorem["positive_root_component_lower_bound"]>0
    assert theorem["finite_dimensional_topological_existence"]
    assert not receipt["explicit_root_computed"]
    assert not receipt["agda_kernel_checked"]


def test_original_formula_weighted_brouwer_rejects_missing_atom_or_unbalance(monkeypatch):
    source,sha,manifest,species,reactions=fixture(monkeypatch)
    certificate=Adapter.load_original_receipt_json(source)
    matrix,_=Adapter.check_certificate(certificate,full_panel=True)
    good={s:({"C":1},0) for s in species}
    for bad in (
        {**good,species[0]:({},0)},
        {**good,species[0]:({"C":2},0)},
        {**good,species[0]:({"C":0.5},0)},
    ):
        monkeypatch.setattr(Adapter,"check_certificate",
                            lambda *a, **kw: (matrix,bad))
        with pytest.raises(ValueError):
            Adapter.source_bound_closed_brouwer_existence(
                source,manifest,pinned_sha256=sha,
                initial_concentrations=np.ones((27,29)),dt=1.0)
