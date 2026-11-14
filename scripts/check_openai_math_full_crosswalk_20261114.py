#!/usr/bin/env python3
"""Fail-closed, offline, exhaustive OpenAI-math ↔ DASHI corpus source audit.

Copies original indexed inventory from Lean #78, and optionally checks both
upstream YAML revisions. A candidate/review is NOT theorem equivalence or
kernel admission. The historical Lean tree scan is explicitly truncated.
"""
import argparse
import copy
import hashlib
import json
import re
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DATA = ROOT / "Docs/roadmaps/OpenAIMathCorpusCrosswalk20261114"
NAMES = {"corpus_declarations_source_index_20261101.json":"cdf408e3a27f367fb2563544888fedd388beab40","corpus_families_source_index_20261101.json":"0bef27841e3a2759e9af69230e2e865ae399b90f","corpus_manuscripts_source_index_20261101.json":"f93e2b24f99503bd46ebaa3a93e49eac7420b5b3","corpus_candidate_owner_routes_20261101.json":"b70c2c299a4af1d296d0f1ac26f71a47c17b2801","reviewed_cross_corpus_same_object_boundaries_20261101.json":"55efb79da001e8904e08890fd55b47e62eb6bffa"}
OLD = "1581d4cbdd69a0faf34b2089614fe2a814316a6a"
NEW = "7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a"
OLD_YAML_SHA = "275eee8cfab7ce49d3a5e88f02cbb8f28fe6fee6"
NEW_YAML_SHA = "372bcd714cd3a186a9139ac8e0f3318961fb2df1"
YAML_ROW = re.compile(
    r"^    - comparator_config: (\\S+)\\r?\\n"
    r"      declaration: ([^\\r\\n]+)\\r?\\n"
    r"      file: ([^\\r\\n]+)", re.M
)

def require(cond, msg):
    if not cond:
        raise ValueError(msg)

def git_blob(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode("ascii") + bytes([0]) + raw).hexdigest()

def parse_yaml(path):
    raw = path.read_bytes()
    source = raw.decode("utf-8")
    require('status:\\n  scope: "Partial progress."' in source,
            "YAML is no longer partial-progress catalogue")
    return YAML_ROW.findall(source), git_blob(raw)

def load(directory=DATA):
    objs = {}
    for filename, blob in NAMES.items():
        raw = (directory / filename).read_bytes()
        require(git_blob(raw) == blob, "historical donor source-byte drift: " + filename)
        objs[filename.split("_source_index")[0] if False else filename] = json.loads(raw)
    return objs

def validate(x):
    dec = x["corpus_declarations_source_index_20261101.json"]
    fam = x["corpus_families_source_index_20261101.json"]
    man = x["corpus_manuscripts_source_index_20261101.json"]
    cand = x["corpus_candidate_owner_routes_20261101.json"]
    rev = x["reviewed_cross_corpus_same_object_boundaries_20261101.json"]
    for title, data, count, key in [
        ("declarations", dec, 208, "declarations"),
        ("families", fam, 373, "families"),
        ("manuscripts", man, 721, "manuscripts"),
    ]:
        require(data["upstream"] == "openai/math", title+" wrong upstream")
        require(data["revision"] == NEW, title+" wrong source revision")
        require(data["source_main_results_blob"] == NEW_YAML_SHA,
                title+" wrong catalogue pin")
        require(data["count"] == count and len(data[key]) == count, title+" count changed")
        require(data["dashi_acceptance"] == "none asserted", title+" false admission")
    declarations = [(e["comparator"], e["declaration"], e["source"])
                    for e in dec["declarations"]]
    require(len(set(declarations)) == 208, "duplicated full indexed declaration")
    require(len({x[0] for x in declarations}) == 192, "wrong comparator count")
    require(all(e["kernel_import"] == "not_verified_in_DASHI"
                and e["same_object"] == "not_established"
                for e in dec["declarations"]), "unsupported source theorem import")
    require(len({e["id"] for e in fam["families"]}) == 373, "duplicate family")
    family_ids = {e["id"] for e in fam["families"]}
    require(all(m["family_id"] in family_ids and
                m["same_object"] == "not_established"
                for m in man["manuscripts"]), "unmatched manuscript or false theorem")
    require(cand["stats"]["rows"] == 208 and len(cand["entries"]) == 208,
            "candidate scan no longer covers exactly 208 declaration refs")
    require(cand["stats"]["verified_matches"] == 0, "lexical scan masquerading as proof")
    require(sum(bool(e["candidates"]) for e in cand["entries"]) == 101,
            "historical lexical hit count changed")
    require(cand["stats"]["with_candidate"] == 101 and
            cand["stats"]["without_candidate"] == 107,
            "historical candidate distribution changed")
    require(any(r["repo"] == "chboishabba/dashi_lean4" and
                r["truncated"] is True for r in cand["source_tree_refs"]),
            "historical truncated Lean search must remain explicit")
    require([(e["comparator"],e["declaration"],e["source"])
             for e in cand["entries"]] == declarations,
            "candidate routing entries no longer aligned with exact catalogue")
    require(len(rev["rows"]) == 6, "six exact source-read reviews are required")
    require(len({r["comparator"] for r in rev["rows"]}) == 6,
            "duplicate source-review comparator")
    for row in rev["rows"]:
        require((row["comparator"],row["source_declaration"],row["source_file"])
                in set(declarations), "review references noncatalogued source")
        require(row["upstream_rev"] == NEW, "review provenance revision mismatch")
        require(row["same_object_transport_paid"] is False and
                row["dashi_kernel_paid"] is False and
                row["comparative_claim_kernel_verified"] is False,
                "review incorrectly promoted to proof")
    require(rev["claims"]["verified_full_ports"] == 0,
            "review makes unsupported global ports claim")
    return {"declarations":208,"comparators":192,"families":373,
            "manuscripts":721,"candidate_rows":101,"unmatched_rows":107,
            "source_read_comparisons":6,"same_object_imports_verified":0,
            "kernel_imports_verified":0,"lean_tree_truncated":True}

def selftest(x):
    validate(x)
    cases = (
        ("false promotion",lambda a:a["reviewed_cross_corpus_same_object_boundaries_20261101.json"]["rows"][0].__setitem__("dashi_kernel_paid", True)),
        ("missing source",lambda a:a["corpus_declarations_source_index_20261101.json"]["declarations"].pop()),
        ("stale reference",lambda a:a["corpus_candidate_owner_routes_20261101.json"]["entries"][0].__setitem__("source","NOT-THE-SAME")),
        ("wrong identity",lambda a:a["corpus_families_source_index_20261101.json"].__setitem__("revision",OLD)),
        ("false exhaustive scan",lambda a:a["corpus_candidate_owner_routes_20261101.json"]["source_tree_refs"][1].__setitem__("truncated",False)),
        ("invented reviewed proof",lambda a:a["reviewed_cross_corpus_same_object_boundaries_20261101.json"]["claims"].__setitem__("verified_full_ports",1)),
    )
    for label,mutate in cases:
        copyx=copy.deepcopy(x)
        mutate(copyx)
        try:
            validate(copyx)
        except (ValueError,KeyError,TypeError):
            pass
        else:
            raise ValueError("negative control unexpectedly accepted: "+label)
    return len(cases)

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--data-dir",type=Path,default=DATA)
    ap.add_argument("--pinned-yaml",type=Path,help="openai/math@1581... lean/formalization.yaml")
    ap.add_argument("--indexed-yaml",type=Path,help="openai/math@7ef5... lean/formalization.yaml")
    ap.add_argument("--self-test",action="store_true")
    args=ap.parse_args()
    require((args.pinned_yaml is None)==(args.indexed_yaml is None),
            "must provide BOTH historical and later pinned YAML to compare")
    obj=load(args.data_dir)
    report=validate(obj)
    if args.self_test:
        report["negative_controls"]=selftest(obj)
    if args.pinned_yaml:
        old, oldblob=parse_yaml(args.pinned_yaml)
        new, newblob=parse_yaml(args.indexed_yaml)
        dec=obj["corpus_declarations_source_index_20261101.json"]
        actual=[(r["comparator"],r["declaration"],r["source"])
                for r in dec["declarations"]]
        require(oldblob==OLD_YAML_SHA and newblob==NEW_YAML_SHA,
                "wrong raw YAML source bytes")
        require(len(old)==200 and len(set(x[0] for x in old))==189,
                "expected old pinned corpus 200/189")
        require(len(new)==208 and len(set(x[0] for x in new))==192,
                "expected later indexed corpus 208/192")
        require(new==actual,"later YAML and current declaration-index differ")
        additions=[r for r in new if r not in set(old)]
        require(len(additions)==8 and all(r in new for r in old),
                "unexpected upstream drift in source main results")
        report["pinned_yaml_verified"]=True
        report["later_yaml_verified"]=True
        report["added_declarations"]=[list(e) for e in additions]
    else:
        report["pinned_yaml_verified"]=False
        report["later_yaml_verified"]=False
    report.update({"result":"PASS","provenance_verified":True,
                   "semantic_compatibility_proved":False,
                   "kernel_checked":False,"agda_theorem_imported":False})
    print(json.dumps(report,indent=2))
if __name__=="__main__":
    try: main()
    except (KeyError,ValueError,TypeError,OSError,UnicodeError) as exc:
        print("FAIL_CLOSED:",exc,file=sys.stderr)
        sys.exit(1)
