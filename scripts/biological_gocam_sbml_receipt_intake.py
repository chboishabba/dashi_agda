#!/usr/bin/env python3
"""Read-only GO-CAM/SBML evidence intake for the DASHI biology max-cut.

Preserves source digests and exact identifiers. Refuses inferred semantic joins.
Not a complete GO-CAM LinkML validator, SBML interpreter, model simulator,
SI calibration or PNF database writer. Use gocam-py/libSBML for official schema
validation before promoting external models.
"""
from __future__ import annotations

import argparse
import hashlib
import json
from pathlib import Path
import tempfile
from xml.etree import ElementTree as ET


def digest(data: bytes) -> str:
    return hashlib.sha256(data).hexdigest()


def require_string(value, name: str) -> str:
    if not isinstance(value, str) or not value.strip():
        raise ValueError(f"missing nonempty {name}")
    return value


def read_gocam(path: Path) -> dict:
    raw = path.read_bytes()
    model = json.loads(raw)
    if not isinstance(model, dict):
        raise ValueError("GO-CAM root must be a JSON object")
    model_id = require_string(model.get("id"), "GO-CAM id")
    activities = model.get("activities", [])
    if not isinstance(activities, list):
        raise ValueError("GO-CAM activities must be an array")
    ids = set()
    parsed = []
    for a in activities:
        if not isinstance(a, dict):
            raise ValueError("GO-CAM activity must be an object")
        aid = require_string(a.get("id"), "GO-CAM activity id")
        if aid in ids:
            raise ValueError(f"duplicate GO-CAM activity: {aid}")
        ids.add(aid)
        mf = a.get("molecular_function") or {}
        if not isinstance(mf, dict):
            raise ValueError(f"invalid molecular_function for {aid}")
        arcs = a.get("causal_associations") or []
        if not isinstance(arcs, list):
            raise ValueError(f"invalid causal_associations for {aid}")
        edges = []
        for arc in arcs:
            if not isinstance(arc, dict):
                raise ValueError(f"invalid causal association for {aid}")
            edges.append({
                "predicate": require_string(arc.get("predicate"), "causal predicate"),
                "downstream_activity": require_string(
                    arc.get("downstream_activity"), "downstream activity"
                ),
                "evidence": arc.get("evidence") or [],
            })
        parsed.append({
            "id": aid,
            "enabled_by": a.get("enabled_by"),
            "molecular_function": mf.get("term"),
            "molecular_function_evidence": mf.get("evidence") or [],
            "causal_associations": edges,
        })
    for a in parsed:
        for edge in a["causal_associations"]:
            if edge["downstream_activity"] not in ids:
                raise ValueError(
                    "causal edge references undeclared downstream activity: "
                    + edge["downstream_activity"]
                )
    return {
        "source_format": "GO-CAM LinkML-style JSON (partial lexical intake)",
        "schema_validated": False,
        "sha256": digest(raw),
        "model_id": model_id,
        "title": model.get("title"),
        "status": model.get("status"),
        "taxon": model.get("taxon"),
        "activities": parsed,
        "declared_activity_count": len(parsed),
    }


def local_name(tag: str) -> str:
    return tag.rsplit("}", 1)[-1]


def direct_child(root, name: str):
    for item in root:
        if local_name(item.tag) == name:
            return item
    return None


def list_child(root, list_name: str, item_name: str):
    parent = direct_child(root, list_name)
    if parent is None:
        return []
    return [item for item in parent if local_name(item.tag) == item_name]


def read_sbml(path: Path) -> dict:
    raw = path.read_bytes()
    if b"<!DOCTYPE" in raw.upper() or b"<!ENTITY" in raw.upper():
        raise ValueError("DTD/entity declarations are not accepted")
    root = ET.fromstring(raw)
    if local_name(root.tag) != "sbml":
        raise ValueError("not an SBML root element")
    model = direct_child(root, "model")
    if model is None:
        raise ValueError("SBML model element missing")
    model_id = require_string(model.get("id"), "SBML model id")
    species = []
    for s in list_child(model, "listOfSpecies", "species"):
        species.append({
            "id": require_string(s.get("id"), "species id"),
            "compartment": s.get("compartment"),
            "substance_units": s.get("substanceUnits"),
            "initial_amount": s.get("initialAmount"),
            "initial_concentration": s.get("initialConcentration"),
        })
    parameters = []
    for p in list_child(model, "listOfParameters", "parameter"):
        parameters.append({
            "id": require_string(p.get("id"), "parameter id"),
            "value": p.get("value"),
            "units": p.get("units"),
        })
    reactions = []
    for reaction in list_child(model, "listOfReactions", "reaction"):
        rid = require_string(reaction.get("id"), "reaction id")
        kinetic = direct_child(reaction, "kineticLaw")
        math = direct_child(kinetic, "math") if kinetic is not None else None
        reactions.append({
            "id": rid,
            "reversible": reaction.get("reversible"),
            "kinetic_law_present": math is not None,
            "mathml": ET.tostring(math, encoding="unicode") if math is not None else None,
        })
    for name, records in (
        ("species", species), ("parameters", parameters), ("reactions", reactions)
    ):
        ids = [item["id"] for item in records]
        if len(ids) != len(set(ids)):
            raise ValueError(f"duplicate SBML {name} identifiers")
    return {
        "source_format": "SBML XML lexical intake (not libSBML semantics)",
        "schema_validated": False,
        "sha256": digest(raw),
        "model_id": model_id,
        "sbml_level": root.get("level"),
        "sbml_version": root.get("version"),
        "model_time_units": model.get("timeUnits"),
        "model_extent_units": model.get("extentUnits"),
        "species": species,
        "parameters": parameters,
        "reactions": reactions,
        "warnings": (
            ["kinetic law missing for " + x["id"] for x in reactions
             if not x["kinetic_law_present"]]
            + ["parameter units missing for " + x["id"] for x in parameters
               if not x["units"]]
        ),
    }


def explicit_joins(gocam: dict, sbml: dict, crosswalk: dict) -> list[dict]:
    rows = crosswalk.get("joins")
    if not isinstance(rows, list):
        raise ValueError("crosswalk requires a joins array")
    aids = {x["id"] for x in gocam["activities"]}
    rids = {x["id"] for x in sbml["reactions"]}
    seen = set()
    out = []
    for row in rows:
        if not isinstance(row, dict):
            raise ValueError("crosswalk join must be an object")
        a = require_string(row.get("gocam_activity"), "crosswalk activity")
        r = require_string(row.get("sbml_reaction"), "crosswalk reaction")
        evidence = require_string(row.get("evidence_reference"), "join evidence")
        if a not in aids or r not in rids:
            raise ValueError("join endpoint does not exist in source models")
        if (a, r) in seen:
            raise ValueError("duplicate join")
        seen.add((a, r))
        out.append({
            "gocam_activity": a,
            "sbml_reaction": r,
            "evidence_reference": evidence,
            "interpretation": "source-asserted candidate; not model equivalence",
            "trusted": False,
        })
    return out


def build_receipt(go_path: Path, sbml_path: Path, crosswalk_path: Path | None = None):
    gocam = read_gocam(go_path)
    sbml = read_sbml(sbml_path)
    joins = []
    if crosswalk_path is not None:
        crosswalk = json.loads(crosswalk_path.read_text())
        if not isinstance(crosswalk, dict):
            raise ValueError("crosswalk root must be an object")
        joins = explicit_joins(gocam, sbml, crosswalk)
    return {
        "status": "unpromoted-source-intake",
        "gocam": gocam,
        "sbml": sbml,
        "candidate_joins": joins,
        "go_cam_model_to_sbml_model_identity_proven": False,
        "biological_calibration_proven": False,
        "pnf_mutation_performed": False,
    }


def self_test():
    with tempfile.TemporaryDirectory() as tmp:
        root = Path(tmp)
        go, sbml, crosswalk = (
            root / "model.json", root / "model.xml", root / "join.json"
        )
        go.write_text(json.dumps({
            "id": "gomodel:test", "title": "Synthetic test", "status": "test",
            "activities": [
                {"id": "gomodel:test/a", "enabled_by": "X:1",
                 "molecular_function": {
                     "term": "GO:0003824",
                     "evidence": [{"term": "ECO:0000314", "reference": "PMID:1"}]},
                 "causal_associations": [{
                     "predicate": "RO:0002629",
                     "downstream_activity": "gomodel:test/b",
                     "evidence": [{"reference": "PMID:1"}]}]},
                {"id": "gomodel:test/b", "causal_associations": []},
            ]}))
        sbml.write_text(
            '<sbml xmlns="http://www.sbml.org/sbml/level3/version2/core"'
            ' level="3" version="2"><model id="toy" timeUnits="second"'
            ' extentUnits="mole"><listOfParameters>'
            '<parameter id="k" value="1" units="per_second"/>'
            '</listOfParameters><listOfReactions><reaction id="r1">'
            '<kineticLaw><math xmlns="http://www.w3.org/1998/Math/MathML">'
            '<ci>k</ci></math></kineticLaw></reaction>'
            '</listOfReactions></model></sbml>'
        )
        crosswalk.write_text(json.dumps({"joins": [{
            "gocam_activity": "gomodel:test/a",
            "sbml_reaction": "r1",
            "evidence_reference": "PMID:1",
        }]}))
        receipt = build_receipt(go, sbml, crosswalk)
        assert len(receipt["candidate_joins"]) == 1
        assert receipt["candidate_joins"][0]["trusted"] is False
        assert receipt["gocam"]["activities"][0]["causal_associations"][0][
            "downstream_activity"] == "gomodel:test/b"
        assert receipt["sbml"]["reactions"][0]["kinetic_law_present"]
        assert receipt["pnf_mutation_performed"] is False
        crosswalk.write_text(json.dumps({"joins": [{
            "gocam_activity": "gomodel:test/a",
            "sbml_reaction": "DOES-NOT-EXIST",
            "evidence_reference": "PMID:1",
        }]}))
        try:
            build_receipt(go, sbml, crosswalk)
        except ValueError:
            pass
        else:
            raise AssertionError("missing join endpoint was accepted")
    print("PASS: GO-CAM / SBML typed lexical intake, evidence join, fail-closed")
    print("NO schema, SI, kinetic, PNF or empirical promotion performed")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--gocam", type=Path)
    parser.add_argument("--sbml", type=Path)
    parser.add_argument("--crosswalk", type=Path)
    parser.add_argument("--output", type=Path)
    parser.add_argument("--self-test", action="store_true")
    args = parser.parse_args()
    if args.self_test:
        self_test()
        return
    if args.gocam is None or args.sbml is None:
        parser.error("--gocam and --sbml are required unless --self-test")
    payload = json.dumps(
        build_receipt(args.gocam, args.sbml, args.crosswalk),
        indent=2, sort_keys=True
    )
    if args.output:
        args.output.write_text(payload + "\n")
    else:
        print(payload)


if __name__ == "__main__":
    main()
