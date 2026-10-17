#!/usr/bin/env python3
"""Execute the Phase-4 BH4 quantitative max-cut pipeline.

The default path performs live public acquisition where appropriate:
  exact UniProt panel -> Rhea/ChEBI -> finite matrix S
  -> 56-coordinate quantitative template (15 core + 12 v + 29 e)
  -> SABIO-RK kinetic candidates
  -> PDBe/SIFTS structural mappings
  -> interval steady-state feasibility
  -> aggregate static regressions

A user-supplied --manifest is normalized against the live matrix before solving.
Candidate external evidence is never automatically promoted into flux bounds.
"""

from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path


def run(cmd: list[str], *, allow_partial: bool = False) -> int:
    print("+", " ".join(cmd), flush=True)
    completed = subprocess.run(cmd)
    if completed.returncode and not allow_partial:
        raise SystemExit(completed.returncode)
    return completed.returncode


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--panel", type=Path, default=Path("artifacts/biology/uniprot-kitzerow-bh4-panel-certificate.json"))
    parser.add_argument("--artifact-dir", type=Path, default=Path("artifacts/biology"))
    parser.add_argument("--manifest", type=Path, help="optional filled quantitative manifest to normalize and solve")
    parser.add_argument("--max-pdb-per-protein", type=int, default=3)
    parser.add_argument("--skip-network-evidence", action="store_true", help="skip SABIO/SIFTS only; Rhea chemistry still refreshes")
    args = parser.parse_args()

    py = sys.executable
    out = args.artifact_dir
    out.mkdir(parents=True, exist_ok=True)

    rhea = out / "rhea-kitzerow-bh4-reactions.json"
    matrix_prefix = out / "bh4-stoichiometric-matrix"
    matrix = matrix_prefix.with_suffix(".json")
    parameter_template = out / "bh4-parameter-template-v2.json"
    normalized_parameters = out / "bh4-parameter-normalized.json"
    sabio = out / "bh4-sabio-kinetics.json"
    sifts = out / "bh4-pdbe-sifts.json"
    interval = out / "bh4-interval-flux-feasibility.json"

    run([py, "scripts/acquire_rhea_chebi_bh4_reactions.py", "--from-uniprot-panel", str(args.panel), "-o", str(rhea)])
    run([py, "scripts/build_bh4_stoichiometric_matrix.py", str(rhea), "--output-prefix", str(matrix_prefix)])
    run([py, "scripts/acquire_bh4_parameter_evidence.py", "--template", "--matrix", str(matrix), "-o", str(parameter_template)])

    solver_parameters = parameter_template
    if args.manifest:
        run([py, "scripts/acquire_bh4_parameter_evidence.py", "--manifest", str(args.manifest), "--matrix", str(matrix), "-o", str(normalized_parameters)])
        solver_parameters = normalized_parameters

    network_exit = {}
    if not args.skip_network_evidence:
        network_exit["sabio"] = run([py, "scripts/acquire_bh4_sabio_kinetics.py", "--panel", str(args.panel), "-o", str(sabio)], allow_partial=True)
        network_exit["sifts"] = run([py, "scripts/acquire_bh4_pdbe_sifts.py", "--panel", str(args.panel), "--max-pdb-per-protein", str(args.max_pdb_per_protein), "-o", str(sifts)], allow_partial=True)

    run([py, "scripts/solve_bh4_flux_intervals.py", "--matrix", str(matrix), "--parameters", str(solver_parameters), "-o", str(interval)], allow_partial=True)
    run([py, "scripts/check_kitzerow_bh4_priority_all.py"])

    matrix_payload = json.loads(matrix.read_text(encoding="utf-8"))
    parameter_payload = json.loads(solver_parameters.read_text(encoding="utf-8"))
    interval_payload = json.loads(interval.read_text(encoding="utf-8"))
    summary = {
        "schema": "dashi.bh4-phase4-maxcut-run.v1",
        "panel": str(args.panel),
        "matrix": {
            "species": len(matrix_payload.get("species_index", [])),
            "reactions": len(matrix_payload.get("reaction_index", [])),
            "residual_reactions": len(matrix_payload.get("finite_formula_residuals", [])),
        },
        "parameters": parameter_payload.get("summary", {"total_coordinates": len(parameter_payload.get("parameters", []))}),
        "interval_status": interval_payload.get("status"),
        "missing_reaction_bounds": len(interval_payload.get("missing_reaction_bounds", [])),
        "missing_exchange_bounds": len(interval_payload.get("missing_exchange_bounds", [])),
        "network_evidence_exit_codes": network_exit,
        "artifacts": {
            "rhea": str(rhea),
            "matrix": str(matrix),
            "parameters": str(solver_parameters),
            "sabio": str(sabio) if not args.skip_network_evidence else None,
            "sifts": str(sifts) if not args.skip_network_evidence else None,
            "interval": str(interval),
        },
    }
    summary_path = out / "bh4-phase4-maxcut-summary.json"
    summary_path.write_text(json.dumps(summary, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    print(json.dumps(summary, indent=2, sort_keys=True))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
