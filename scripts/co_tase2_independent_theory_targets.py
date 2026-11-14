"""Validate independent theory targets for CoTa4Se8 == Co1/4TaSe2.

This is a publication-target receipt.  It does not manufacture a material
Hamiltonian, raw ARPES observer, or quantitative same-object fit.
"""
import argparse
import json
from pathlib import Path


def validate(path):
    p = Path(path)
    d = json.loads(p.read_text())
    assert d["source"]["doi"] == "10.1038/s41535-026-00885-5"
    assert d["source"]["compound_label"] == "CoTa4Se8"
    assert d["source"]["same_stoichiometry_as"] == "Co1/4TaSe2"
    assert d["dft"]["code"] == "VASP"
    assert d["dft"]["core_valence"] == "PAW"
    assert d["dft"]["plane_wave_cutoff_ev"] == 450
    assert d["dft"]["k_mesh"] == [9, 9, 4]
    assert d["dft"]["supercell"] == [2, 2, 1]
    assert d["altermagnet_targets"]["nodal_plane_kz"] == "0"
    assert d["altermagnet_targets"]["off_nodal_plane_kz"] == "pi/(2c)"
    assert d["altermagnet_targets"]["off_nodal_split_path"] == "Gamma'-M'"
    assert d["altermagnet_targets"]["soc_included"] is True
    assert d["altermagnet_targets"]["co_ta4_se8_split_mev_at_ef_approx"] == 110
    assert d["altermagnet_targets"]["co_ta4_se8_split_mev_at_minus_0_25_ev_approx"] == 154
    assert d["kagome_like_tb"]["sites"] == 4
    assert d["kagome_like_tb"]["kagome_like_sites"] == [2, 3, 4]
    assert d["producer_method_donor"]["doi"] == "10.1103/PhysRevB.107.184429"
    assert d["producer_method_donor"]["executed_for_literal_current_artifact"] is False
    b = d["promotion_boundary"]
    assert b["same_object_material_hamiltonian_closed"] is False
    assert b["raw_arpes_closed"] is False
    assert b["quantitative_fit_closed"] is False
    assert b["independent_acceptance_targets_paid"] is True
    assert b["wannier_producer_design_route_paid"] is True
    return {
        "source_doi": d["source"]["doi"],
        "same_stoichiometry": True,
        "soc_target_paid": True,
        "nodal_off_nodal_target_paid": True,
        "published_split_targets_mev": [110, 154],
        "kagome_like_tb_target_paid": True,
        "wannier_producer_route_paid": True,
        "literal_material_hamiltonian_closed": False,
        "raw_arpes_closed": False,
        "quantitative_fit_closed": False,
    }


if __name__ == "__main__":
    ap = argparse.ArgumentParser()
    ap.add_argument("targets")
    ap.add_argument("--receipt")
    a = ap.parse_args()
    out = validate(a.targets)
    if a.receipt:
        Path(a.receipt).write_text(json.dumps(out, indent=2) + "\n")
    print(json.dumps(out, indent=2))
