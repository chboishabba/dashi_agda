#!/usr/bin/env python3
"""
Generate an Agda module from HME CLI JSON output.
Input JSON schema: produced by scripts/hme_cli.py.
Writes DASHI/HME/Generated/Witnesses.agda (overwrite).
Does not touch Everything.agda; import manually if desired.
"""

import argparse
import json
from pathlib import Path
from typing import Any, Dict, List

TEMPLATE = """module DASHI.HME.Generated.Witnesses where

open import Agda.Builtin.Bool using (Bool)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.String using (String)
open import Agda.Builtin.List using (List; []; _∷_)
open import Data.Product using (_×_; _,_)

open import DASHI.HME.Trace

canonicalWitnesses : List CanonicalWitness
canonicalWitnesses = {witness_list}

clusterAssignments : List Float
clusterAssignments = {cluster_list}

silhouette : Float
silhouette = {sil}

invarianceScore : Float
invarianceScore = {inv}
"""


def to_list(lst: List[Any]) -> str:
    if not lst:
        return "[]"
    return "(" + " ∷ ".join(str(x) for x in lst) + " ∷ [])"


def render_witness(w: Dict[str, Any]) -> str:
    inv_pairs = w.get("invariants", {})
    inv_list = " ∷ ".join([f'( "{k}" , {float(v)} )' for k, v in inv_pairs.items()])
    inv_list = "(" + inv_list + " ∷ [])" if inv_pairs else "[]"
    rv = w.get("residue_vector", [])
    rv_list = " ∷ ".join([str(float(x)) for x in rv])
    rv_list = "(" + rv_list + " ∷ [])" if rv else "[]"
    sig = w.get("proof_signature", "")
    return f'record {{ traceId = "{w.get("trace_id","")}" ; residueVector = {rv_list} ; basinId = {int(w.get("basin_id",0))} ; invariants = {inv_list} ; proofSignature = "{sig}" }}'


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("json", help="hme_cli output JSON")
    ap.add_argument("--out", default="DASHI/HME/Generated/Witnesses.agda", help="output Agda module path")
    args = ap.parse_args()

    with open(args.json, "r", encoding="utf-8") as f:
        data = json.load(f)

    cw = data.get("canonical_witnesses", [])
    cluster = data.get("cluster_assignments", [])
    sil = float(data.get("silhouette", 0.0))
    inv = float(data.get("invariance_score", 0.0))

    witness_list = " ∷ ".join(render_witness(w) for w in cw)
    witness_list = "(" + witness_list + " ∷ [])" if cw else "[]"

    cluster_list = to_list([float(x) for x in cluster])

    out_text = TEMPLATE.format(
        witness_list=witness_list,
        cluster_list=cluster_list,
        sil=sil,
        inv=inv,
    )

    out_path = Path(args.out)
    out_path.parent.mkdir(parents=True, exist_ok=True)
    out_path.write_text(out_text, encoding="utf-8")


if __name__ == "__main__":
    main()
