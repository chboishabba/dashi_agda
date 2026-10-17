#!/usr/bin/env python3
"""Execute the Phase-4 BH4 quantitative max-cut pipeline."""
from __future__ import annotations
import argparse, json, subprocess, sys
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
    p.add_argument("--max-pdb-per-protein", type=int, default=3)
    p.add_argument("--top-kinetic-candidates", type=int, default=10)
    p.add_argument("--skip-network-evidence", action="store_true")
    a = p.parse_args(); py = sys.executable; out = a.artifact_dir; out.mkdir(parents=True, exist_ok=True)
    rhea=out/"rhea-kitzerow-bh4-reactions.json"; mp=out/"bh4-stoichiometric-matrix"; matrix=mp.with_suffix(".json")
    template=out/"bh4-parameter-template-v2.json"; norm=out/"bh4-parameter-normalized.json"
    sabio=out/"bh4-sabio-kinetics.json"; adj=out/"bh4-sabio-adjudication.json"; ranking=out/"bh4-flux-candidate-ranking.json"
    payment=out/"bh4-flux-payment-preparation.json"; sifts=out/"bh4-pdbe-sifts.json"; interval=out/"bh4-interval-flux-feasibility.json"; summary_path=out/"bh4-phase4-maxcut-summary.json"
    run([py,"scripts/acquire_rhea_chebi_bh4_reactions.py","--from-uniprot-panel",str(a.panel),"-o",str(rhea)])
    run([py,"scripts/build_bh4_stoichiometric_matrix.py",str(rhea),"--output-prefix",str(mp)])
    run([py,"scripts/acquire_bh4_parameter_evidence.py","--template","--matrix",str(matrix),"-o",str(template)])
    solver=template
    if a.manifest:
        run([py,"scripts/acquire_bh4_parameter_evidence.py","--manifest",str(a.manifest),"--matrix",str(matrix),"-o",str(norm)]); solver=norm
    exits={}
    if not a.skip_network_evidence:
        exits["sabio"]=run([py,"scripts/acquire_bh4_sabio_kinetics.py","--panel",str(a.panel),"-o",str(sabio)],allow_partial=True)
        if exits["sabio"]==0 and sabio.exists():
            exits["sabio_adjudication"]=run([py,"scripts/build_bh4_sabio_adjudication.py","--sabio",str(sabio),"--rhea",str(rhea),"--matrix",str(matrix),"-o",str(adj)],allow_partial=True)
            if exits["sabio_adjudication"]==0 and adj.exists():
                exits["sabio_flux_ranking"]=run([py,"scripts/rank_bh4_flux_candidates.py","--adjudication",str(adj),"--matrix",str(matrix),"--top-n",str(a.top_kinetic_candidates),"-o",str(ranking)],allow_partial=True)
                if exits["sabio_flux_ranking"]==0 and ranking.exists():
                    exits["sabio_flux_payment"]=run([py,"scripts/prepare_bh4_flux_payment.py","--ranking",str(ranking),"-o",str(payment)],allow_partial=True)
        exits["sifts"]=run([py,"scripts/acquire_bh4_pdbe_sifts.py","--panel",str(a.panel),"--max-pdb-per-protein",str(a.max_pdb_per_protein),"-o",str(sifts)],allow_partial=True)
    interval_exit=run([py,"scripts/solve_bh4_flux_intervals.py","--matrix",str(matrix),"--parameters",str(solver),"-o",str(interval)],allow_partial=True)
    run([py,"scripts/check_kitzerow_bh4_priority_all.py"])
    m=json.loads(matrix.read_text()); params=json.loads(solver.read_text()); inter=json.loads(interval.read_text())
    sab=load(sabio); ad=load(adj); rk=load(ranking); pay=load(payment); sf=load(sifts)
    network={}
    if sab: network["sabio"]={k:sab.get(k) for k in ("schema","proteins_completed","proteins_with_entries","kinetic_entry_count","kinetic_parameter_count")}
    if ad: network["sabio_adjudication"]={k:ad.get(k) for k in ("schema","parameter_candidate_count","parameter_candidates_mapped_to_finite_matrix","finite_reaction_candidate_coverage","uncovered_finite_reactions","parameter_kind_counts")}
    if rk: network["sabio_flux_ranking"]={k:rk.get(k) for k in ("schema","finite_reaction_count","finite_reactions_with_any_candidate","payable_reaction_count","blocked_reaction_count","payable_reactions","blocked_reactions")}
    if pay: network["sabio_flux_payment"]={k:pay.get(k) for k in ("schema","finite_reaction_count","evidence_class_counts","enzyme_abundance_required_reactions","normalization_bridge_required_reactions","magnitude_anchor_missing_reactions","payable_reaction_count")}
    if sf: network["sifts"]={**(sf.get("summary") or {}),"schema":sf.get("schema")}
    summary={"schema":"dashi.bh4-phase4-maxcut-run.v6","panel":str(a.panel),"matrix":{"species":len(m.get("species_index",[])),"reactions":len(m.get("reaction_index",[])),"residual_reactions":len(m.get("finite_formula_residuals",[]))},"parameters":params.get("summary",{}),"interval_status":inter.get("status"),"interval_exit_code":interval_exit,"missing_reaction_bounds":len(inter.get("missing_reaction_bounds",[])),"missing_exchange_bounds":len(inter.get("missing_exchange_bounds",[])),"network_evidence_exit_codes":exits,"network_evidence":network,"artifacts":{"rhea":str(rhea),"matrix":str(matrix),"parameter_template":str(template),"parameters_used_by_solver":str(solver),"sabio":str(sabio),"sabio_adjudication":str(adj),"sabio_flux_ranking":str(ranking),"sabio_flux_payment":str(payment),"sifts":str(sifts),"interval":str(interval),"summary":str(summary_path)}}
    summary_path.write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n"); print(json.dumps(summary,indent=2,sort_keys=True))
    return 3 if inter.get("status")=="infeasible" else 0

if __name__ == "__main__": raise SystemExit(main())
