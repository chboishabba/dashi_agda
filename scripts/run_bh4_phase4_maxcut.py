#!/usr/bin/env python3
"""Execute the Phase-4 BH4 quantitative max-cut pipeline."""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def run(cmd: list[str], *, allow_partial: bool = False) -> int:
    print("+", " ".join(cmd), flush=True)
    c = subprocess.run(cmd)
    if c.returncode and not allow_partial:
        raise SystemExit(c.returncode)
    return c.returncode


def load(path: Path) -> dict | None:
    try:
        return json.loads(path.read_text()) if path.exists() else None
    except Exception:
        return None


def main() -> int:
    p = argparse.ArgumentParser()
    p.add_argument("--panel", type=Path, default=Path("artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json"))
    p.add_argument("--artifact-dir", type=Path, default=Path("artifacts/biology"))
    p.add_argument("--manifest", type=Path)
    p.add_argument("--wikimedia", type=Path, help="optional pinned Wikimedia BH4 panel receipt; no network acquisition is implied")
    p.add_argument("--source-reopen-packet", type=Path, help="optional caller-supplied source/revision references; does not authenticate source text")
    p.add_argument("--creator-source-text", type=Path,
                   help="optional authorized local creator-chart text; source evidence only")
    p.add_argument("--acquire-creator-chart-reactions", action="store_true",
                   help="opt in to separate source-chart Rhea/ChEBI acquisition; no merger with panel")
    p.add_argument("--creator-source-revision", type=str,
                   help="required with --creator-source-text; observed date/source, not authentication")
    p.add_argument("--max-pdb-per-protein", type=int, default=3)
    p.add_argument("--top-kinetic-candidates", type=int, default=10)
    p.add_argument("--skip-network-evidence", action="store_true")
    a = p.parse_args()
    py = sys.executable
    out = a.artifact_dir
    out.mkdir(parents=True, exist_ok=True)

    rhea = out / "rhea-kitzerow-bh4-reactions.json"
    mp = out / "bh4-stoichiometric-matrix"
    matrix = mp.with_suffix(".json")
    template = out / "bh4-parameter-template-v2.json"
    norm = out / "bh4-parameter-normalized.json"
    sabio = out / "bh4-sabio-kinetics.json"
    adj = out / "bh4-sabio-adjudication.json"
    ranking = out / "bh4-flux-candidate-ranking.json"
    payment = out / "bh4-flux-payment-preparation.json"
    abundance = out / "bh4-protein-abundance.json"
    exchange_context = out / "bh4-exchange-context.json"
    joint_payment = out / "bh4-joint-payment-ledger.json"
    sifts = out / "bh4-pdbe-sifts.json"
    xpollenation = out / "bh4-xpollenation.json"
    xpollenation_dir = out / "xpollenation-neighbourhoods"
    ontology = out / "bh4-pathway-ontology.json"
    ontology_jsonld = out / "bh4-pathway-ontology.jsonld"
    ontology_review = out / "bh4-pathway-review-worklist.json"
    primary_chart_crosswalk = out / "kitzerow-primary-chart-rhea-crosswalk.json"
    creator_chart_text_index = out / "kitzerow-chart-source-text-candidates.json"
    creator_chart_rhea = out / "kitzerow-creator-chart-rhea-reactions.json"
    creator_chart_matrix_prefix = out / "kitzerow-creator-chart-stoichiometric-matrix"
    creator_chart_matrix = creator_chart_matrix_prefix.with_suffix(".json")
    claim_ledger = Path("docs/biology/KitzerowBH4ClaimLedgerCandidate.v1.json")
    interval = out / "bh4-interval-flux-feasibility.json"
    summary_path = out / "bh4-phase4-maxcut-summary.json"

    run([py, "scripts/acquire_rhea_chebi_bh4_reactions.py", "--from-uniprot-panel", str(a.panel), "-o", str(rhea)])
    run([py, "scripts/build_bh4_stoichiometric_matrix.py", str(rhea), "--output-prefix", str(mp)])
    if bool(a.creator_source_text) != bool(a.creator_source_revision):
        raise SystemExit("--creator-source-text and --creator-source-revision must occur together")
    compare_cmd = [
        py, "scripts/compare_kitzerow_primary_chart.py",
        "--matrix", str(matrix), "-o", str(primary_chart_crosswalk),
    ]
    if a.creator_source_text:
        run([
            py, "scripts/index_kitzerow_chart_source_text.py",
            "--source-text", str(a.creator_source_text),
            "--source-revision", a.creator_source_revision,
            "-o", str(creator_chart_text_index),
        ])
        compare_cmd.extend(["--source-text-index", str(creator_chart_text_index)])
    run(compare_cmd)
    run([py, "scripts/check_kitzerow_primary_chart.py"])
    run([py, "scripts/check_kitzerow_source_chart_acquisition.py"])
    creator_chart_acquisition_exit: int | None = None
    if a.acquire_creator_chart_reactions:
        creator_chart_acquisition_exit = run([
            py, "scripts/acquire_rhea_chebi_bh4_reactions.py",
            "--from-source-chart",
            "docs/biology/KitzerowPublishedRheaChartObservedIndex.v1.json",
            "-o", str(creator_chart_rhea),
        ], allow_partial=True)
        if creator_chart_rhea.exists():
            # A missing or nonfinite creator reaction is a residual, not
            # automatically a zero-valued internal reaction.
            run([
                py, "scripts/build_bh4_stoichiometric_matrix.py",
                str(creator_chart_rhea),
                "--output-prefix", str(creator_chart_matrix_prefix),
            ])
    run([py, "scripts/acquire_bh4_parameter_evidence.py", "--template", "--matrix", str(matrix), "-o", str(template)])
    solver = template
    if a.manifest:
        run([py, "scripts/acquire_bh4_parameter_evidence.py", "--manifest", str(a.manifest), "--matrix", str(matrix), "-o", str(norm)])
        solver = norm

    exits: dict[str, int] = {}
    if not a.skip_network_evidence:
        exits["sabio"] = run([py, "scripts/acquire_bh4_sabio_kinetics.py", "--panel", str(a.panel), "-o", str(sabio)], allow_partial=True)
        if exits["sabio"] == 0 and sabio.exists():
            exits["sabio_adjudication"] = run([py, "scripts/build_bh4_sabio_adjudication.py", "--sabio", str(sabio), "--rhea", str(rhea), "--matrix", str(matrix), "-o", str(adj)], allow_partial=True)
            if exits["sabio_adjudication"] == 0 and adj.exists():
                exits["sabio_flux_ranking"] = run([py, "scripts/rank_bh4_flux_candidates.py", "--adjudication", str(adj), "--matrix", str(matrix), "--top-n", str(a.top_kinetic_candidates), "-o", str(ranking)], allow_partial=True)
                if exits["sabio_flux_ranking"] == 0 and ranking.exists():
                    exits["sabio_flux_payment"] = run([py, "scripts/prepare_bh4_flux_payment.py", "--ranking", str(ranking), "-o", str(payment)], allow_partial=True)
        exits["protein_abundance"] = run([py, "scripts/acquire_bh4_protein_abundance.py", "--panel", str(a.panel), "-o", str(abundance)], allow_partial=True)
        exits["exchange_context"] = run([py, "scripts/acquire_bh4_exchange_context.py", "--matrix", str(matrix), "--rhea", str(rhea), "-o", str(exchange_context)], allow_partial=True)
        exits["sifts"] = run([py, "scripts/acquire_bh4_pdbe_sifts.py", "--panel", str(a.panel), "--max-pdb-per-protein", str(a.max_pdb_per_protein), "-o", str(sifts)], allow_partial=True)

        if payment.exists() and abundance.exists() and exchange_context.exists():
            exits["joint_payment"] = run([
                py, "scripts/build_bh4_joint_payment_ledger.py",
                "--matrix", str(matrix), "--payment", str(payment),
                "--abundance", str(abundance), "--exchange", str(exchange_context),
                "--parameters", str(solver), "-o", str(joint_payment),
            ], allow_partial=True)

    if adj.exists():
        xp_cmd = [
            py, "scripts/build_bh4_xpollenation.py",
            "--matrix", str(matrix), "--rhea", str(rhea),
            "--adjudication", str(adj), "-o", str(xpollenation),
            "--neighbourhood-dir", str(xpollenation_dir),
        ]
        if sifts.exists():
            xp_cmd.extend(["--sifts", str(sifts)])
        if abundance.exists():
            xp_cmd.extend(["--abundance", str(abundance)])
        if exchange_context.exists():
            xp_cmd.extend(["--exchange-context", str(exchange_context)])
        if a.wikimedia is not None and a.wikimedia.exists():
            xp_cmd.extend(["--wikimedia", str(a.wikimedia)])
        exits["xpollenation"] = run(xp_cmd, allow_partial=True)
        if exits["xpollenation"] == 0:
            run([py, "scripts/check_bh4_xpollenation.py"])

    ontology_cmd = [
        py, "scripts/build_bh4_pathway_ontology.py",
        "--matrix", str(matrix), "--rhea", str(rhea),
        "--claims", str(claim_ledger), "-o", str(ontology),
        "--jsonld-output", str(ontology_jsonld),
    ]
    if exits.get("xpollenation") == 0 and xpollenation.exists():
        ontology_cmd.extend(["--xpollenation", str(xpollenation)])
    exits["pathway_ontology"] = run(ontology_cmd, allow_partial=True)
    if exits["pathway_ontology"] == 0:
        run([py, "scripts/check_bh4_pathway_ontology.py"])

    if exits.get("pathway_ontology") == 0:
        review_cmd = [
            py, "scripts/build_bh4_pathway_review.py",
            "--pathway", str(ontology), "-o", str(ontology_review),
        ]
        if a.source_reopen_packet is not None:
            review_cmd.extend(["--source-receipts", str(a.source_reopen_packet)])
        exits["pathway_review"] = run(review_cmd, allow_partial=True)
        if exits["pathway_review"] == 0:
            run([py, "scripts/check_bh4_pathway_review.py"])

    interval_exit = run([py, "scripts/solve_bh4_flux_intervals.py", "--matrix", str(matrix), "--parameters", str(solver), "-o", str(interval)], allow_partial=True)
    run([py, "scripts/check_kitzerow_bh4_priority_all.py"])

    m = json.loads(matrix.read_text())
    params = json.loads(solver.read_text())
    inter = json.loads(interval.read_text())
    sab = load(sabio); ad = load(adj); rk = load(ranking); pay = load(payment)
    abund = load(abundance); exch = load(exchange_context); joint = load(joint_payment)
    sf = load(sifts); xp = load(xpollenation); ont = load(ontology) if exits.get("pathway_ontology") == 0 else None
    review = load(ontology_review) if exits.get("pathway_review") == 0 else None
    original_chart = load(primary_chart_crosswalk)
    creator_acquisition = (load(creator_chart_rhea)
                           if a.acquire_creator_chart_reactions else None)
    creator_matrix = (load(creator_chart_matrix)
                      if a.acquire_creator_chart_reactions else None)
    network: dict[str, object] = {}
    if sab:
        network["sabio"] = {k: sab.get(k) for k in ("schema", "proteins_completed", "proteins_with_entries", "kinetic_entry_count", "kinetic_parameter_count")}
    if ad:
        network["sabio_adjudication"] = {k: ad.get(k) for k in ("schema", "parameter_candidate_count", "parameter_candidates_mapped_to_finite_matrix", "finite_reaction_candidate_coverage", "uncovered_finite_reactions", "parameter_kind_counts")}
    if rk:
        network["sabio_flux_ranking"] = {k: rk.get(k) for k in ("schema", "finite_reaction_count", "finite_reactions_with_any_candidate", "payable_reaction_count", "blocked_reaction_count", "payable_reactions", "blocked_reactions")}
    if pay:
        network["sabio_flux_payment"] = {k: pay.get(k) for k in ("schema", "finite_reaction_count", "evidence_class_counts", "enzyme_abundance_required_reactions", "normalization_bridge_required_reactions", "magnitude_anchor_missing_reactions", "payable_reaction_count")}
    if abund:
        network["protein_abundance"] = {k: abund.get(k) for k in ("schema", "proteins_requested", "proteins_with_observations", "observation_count")}
        network["protein_abundance"]["error_count"] = len(abund.get("errors", []))
    if exch:
        network["exchange_context"] = {k: exch.get(k) for k in ("schema", "species_requested", "species_with_refmet_match", "species_with_human_study_context")}
        network["exchange_context"]["error_count"] = len(exch.get("errors", []))
    if joint:
        network["joint_payment"] = {"schema": joint.get("schema"), **(joint.get("summary") or {})}
    if sf:
        network["sifts"] = {**(sf.get("summary") or {}), "schema": sf.get("schema")}
    if xp:
        network["xpollenation"] = {
            "schema": xp.get("schema"), "reaction_count": xp.get("reaction_count"),
            "neighbourhood_dir": str(xpollenation_dir),
            "authority": "navigation-enrichment-only", "establishes_payment": False,
        }

    if ont:
        network["pathway_ontology"] = {
            "schema": ont.get("schema"),
            "finite_reactions": len(ont.get("reactions", [])),
            "species": len(ont.get("species", [])),
            "unpromoted_hypothesis_edges": len(ont.get("author_hypothesis_edges", [])),
            "external_edges": len(ont.get("external_edges", [])),
            "rhea_go_reactome_cross_references": len(ont.get("ontology_cross_references", [])),
            "authority": ont.get("authority"),
        }

    if creator_acquisition:
        network["kitzerow_creator_chart_rhea_acquisition"] = {
            "schema": creator_acquisition.get("schema"),
            "requested": creator_acquisition.get("unique_rhea_ids_requested"),
            "acquired": creator_acquisition.get("rhea_rows_acquired"),
            "failed": creator_acquisition.get("rhea_rows_failed"),
            "formula_charge_ready": creator_acquisition.get("formula_charge_ready_reactions"),
            "separate_creator_chart_selection": True,
            "original_pdf_binary_verified": False,
            "acquisition_exit_code": creator_chart_acquisition_exit,
            "separate_matrix_species": creator_matrix.get("species_count") if creator_matrix else None,
            "separate_matrix_reactions": creator_matrix.get("reaction_count") if creator_matrix else None,
        }
    if original_chart and original_chart.get("local_source_text_observation"):
        network["creator_chart_local_text_observation"] = {
            "schema": original_chart["local_source_text_observation"]["schema"],
            "source_text_sha256": original_chart["local_source_text_observation"]["source_utf8_sha256"],
            "candidate_observed_ids": original_chart["local_source_text_observation"]["creator_chart_observed_rhea_id_count"],
            "source_is_original_pdf": False,
            "creator_whole_network_coverage": None,
        }
    if original_chart:
        network["kitzerow_original_chart"] = {
            "schema": original_chart.get("schema"),
            "observed_chart_rhea_ids": original_chart.get("creator_chart_observed_rhea_id_count"),
            "finite_panel_ids": original_chart.get("dashi_finite_panel_rhea_id_count"),
            "literal_overlap": len(original_chart.get("literal_rhea_identifier_intersection", [])),
            "whole_creator_network_coverage_ratio": None,
        }
    if review:
        network["pathway_review"] = {
            "schema": review.get("schema"),
            "obligations": len(review.get("obligations", [])),
            "family_counts": review.get("obligation_family_counts", {}),
            "authority": review.get("authority"),
        }

    summary = {
        "schema": "dashi.bh4-phase4-maxcut-run.v8",
        "panel": str(a.panel),
        "matrix": {"species": len(m.get("species_index", [])), "reactions": len(m.get("reaction_index", [])), "residual_reactions": len(m.get("finite_formula_residuals", []))},
        "parameters": params.get("summary", {}),
        "interval_status": inter.get("status"), "interval_exit_code": interval_exit,
        "missing_reaction_bounds": len(inter.get("missing_reaction_bounds", [])),
        "missing_exchange_bounds": len(inter.get("missing_exchange_bounds", [])),
        "network_evidence_exit_codes": exits, "network_evidence": network,
        "artifacts": {
            "rhea": str(rhea), "matrix": str(matrix), "parameter_template": str(template),
            "parameters_used_by_solver": str(solver), "sabio": str(sabio),
            "sabio_adjudication": str(adj), "sabio_flux_ranking": str(ranking),
            "sabio_flux_payment": str(payment), "protein_abundance": str(abundance),
            "exchange_context": str(exchange_context), "joint_payment": str(joint_payment),
            "sifts": str(sifts), "xpollenation": str(xpollenation),
            "xpollenation_neighbourhoods": str(xpollenation_dir),
            "pathway_ontology": str(ontology), "pathway_ontology_jsonld": str(ontology_jsonld),
            "pathway_review": str(ontology_review) if review else None,
            "kitzerow_primary_chart_crosswalk": str(primary_chart_crosswalk),
            "kitzerow_chart_source_text_candidates": str(creator_chart_text_index) if a.creator_source_text else None,
            "kitzerow_creator_chart_rhea": str(creator_chart_rhea) if a.acquire_creator_chart_reactions else None,
            "kitzerow_creator_chart_matrix": str(creator_chart_matrix) if creator_matrix else None,
            "interval": str(interval),
            "summary": str(summary_path),
        },
    }
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 3 if inter.get("status") == "infeasible" else 0


if __name__ == "__main__":
    raise SystemExit(main())
