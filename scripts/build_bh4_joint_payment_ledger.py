#!/usr/bin/env python3
"""Compile reaction, exchange, and state-context payment status into one ledger.

The ledger is descriptive and fail-closed. Protein-abundance intensity and
metabolite concentration/study occurrence are context evidence only; neither is
promoted to a solver flux interval without the existing source/same-object/
compartment/time/unit/payment obligations.
"""
from __future__ import annotations

import argparse, json
from pathlib import Path


def paid_rows(parameters: dict) -> dict[str,dict]:
    return {str(r.get("parameter_id")):r for r in parameters.get("parameters",[]) if r.get("parameter_id")}


def abundance_index(abundance: dict) -> dict[str,dict]:
    return {str(r.get("symbol")):r for r in abundance.get("results",[]) if r.get("symbol")}


def exchange_index(exchange: dict) -> dict[str,dict]:
    return {str(r.get("species")):r for r in exchange.get("species",[]) if r.get("species")}


def build(matrix: dict, payment: dict, abundance: dict, exchange: dict, parameters: dict) -> dict:
    param=paid_rows(parameters); ab=abundance_index(abundance); ex=exchange_index(exchange)
    payment_by_rhea={str(r.get("rhea_id")):r for r in payment.get("reactions",[]) if r.get("rhea_id")}
    reaction_flux_coordinates=[]
    for rid in matrix.get("reaction_index",[]):
        p=payment_by_rhea.get(str(rid),{}); top=p.get("top_candidates") or []
        symbols=sorted({str(c.get("symbol")) for c in top if c.get("symbol")})
        abundance_context=[{
            "symbol":s,
            "observation_count":int((ab.get(s) or {}).get("observation_count") or 0),
            "molecular_weight":(ab.get(s) or {}).get("mol_weight"),
        } for s in symbols]
        manifest=param.get(f"REACTION_FLUX:{rid}",{})
        solver_payable=bool(manifest.get("usable_for_joint_flux_witness"))
        reaction_flux_coordinates.append({
            "rhea_id":rid,
            "parameter_id":f"REACTION_FLUX:{rid}",
            "evidence_class":p.get("evidence_class"),
            "abundance_context":abundance_context,
            "abundance_context_acquired":any(x["observation_count"]>0 for x in abundance_context),
            "abundance_intensity_is_not_enzyme_concentration":True,
            "payment_gates":p.get("payment_gates",{}),
            "solver_payable":solver_payable,
            "manifest_payment_status":manifest.get("payment_status","unresolved"),
        })
    exchange_coordinates=[]
    for species in matrix.get("species_index",[]):
        ctx=ex.get(str(species),{}); manifest=param.get(f"EXCHANGE:{species}",{})
        exchange_coordinates.append({
            "species":species,
            "parameter_id":f"EXCHANGE:{species}",
            "refmet_match_count":len(ctx.get("refmet_matches") or []),
            "human_study_context_count":len(ctx.get("human_studies") or []),
            "concentration_context_is_not_exchange_flux":True,
            "transport_or_turnover_evidence_required":True,
            "solver_payable":bool(manifest.get("usable_for_joint_flux_witness")),
            "manifest_payment_status":manifest.get("payment_status","unresolved"),
        })
    state_context_coordinates=[]
    for row in parameters.get("parameters",[]):
        pid=str(row.get("parameter_id") or "")
        if pid.startswith("REACTION_FLUX:") or pid.startswith("EXCHANGE:"): continue
        state_context_coordinates.append({
            "parameter_id":pid,
            "payment_status":row.get("payment_status"),
            "solver_payable":bool(row.get("usable_for_joint_flux_witness")),
        })
    return {
        "schema":"dashi.bh4-joint-payment-ledger.v1",
        "reaction_flux_coordinates":reaction_flux_coordinates,
        "exchange_coordinates":exchange_coordinates,
        "state_context_coordinates":state_context_coordinates,
        "summary":{
            "reaction_flux_coordinate_count":len(reaction_flux_coordinates),
            "reaction_flux_solver_payable":sum(x["solver_payable"] for x in reaction_flux_coordinates),
            "reaction_flux_with_abundance_context":sum(x["abundance_context_acquired"] for x in reaction_flux_coordinates),
            "exchange_coordinate_count":len(exchange_coordinates),
            "exchange_solver_payable":sum(x["solver_payable"] for x in exchange_coordinates),
            "exchange_with_refmet_context":sum(x["refmet_match_count"]>0 for x in exchange_coordinates),
            "exchange_with_human_study_context":sum(x["human_study_context_count"]>0 for x in exchange_coordinates),
            "state_context_coordinate_count":len(state_context_coordinates),
            "state_context_solver_payable":sum(x["solver_payable"] for x in state_context_coordinates),
        },
        "promotion_boundary":{
            "abundance_intensity_is_not_enzyme_concentration":True,
            "concentration_context_is_not_exchange_flux":True,
            "context_coverage_creates_solver_payment":False,
            "different_tissues_create_same_state":False,
        },
    }


def main() -> int:
    p=argparse.ArgumentParser()
    for arg in ("matrix","payment","abundance","exchange","parameters"): p.add_argument(f"--{arg}",type=Path,required=True)
    p.add_argument("-o","--output",type=Path,required=True); a=p.parse_args()
    obj=lambda x:json.loads(x.read_text(encoding="utf-8"))
    out=build(obj(a.matrix),obj(a.payment),obj(a.abundance),obj(a.exchange),obj(a.parameters))
    a.output.parent.mkdir(parents=True,exist_ok=True); a.output.write_text(json.dumps(out,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps({"schema":out["schema"],**out["summary"]},indent=2,sort_keys=True)); return 0

if __name__ == "__main__": raise SystemExit(main())
