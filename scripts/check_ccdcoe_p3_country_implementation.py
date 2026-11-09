#!/usr/bin/env python3
"""Fail-closed original-source country/commitment implementation join.

No country outcomes are bundled. A join is an admitted, attributed
observation only, not a causal estimate or a common longitudinal cohort.
Input JSON has schema dashi.ccdcoe.p3.country_join.v1 and 'records'.
Each record supplies source-byte evidence, independently reviewed exact
span, study and commitment identity, country, interval, and metric units.
Use --self-test for synthetic negative controls (not empirical acceptance).
"""
import argparse
import hashlib
import json
from pathlib import Path

SCHEMA = "dashi.ccdcoe.p3.country_join.v1"
METRICS = {"compliance_score", "ndc_procedural", "emissions", "finance"}
STUDIES = {"brisbane2014_final_G20RG", "antalya2015_final_G20RG"}
def require(cond, msg):
    if not cond:
        raise ValueError(msg)

def safe_path(root, value):
    require(isinstance(value, str) and value and not Path(value).is_absolute(), "unsafe relative path")
    root = root.resolve()
    path = (root / value).resolve()
    require(path != root and root in path.parents and path.is_file(), "missing/escaping source path")
    return path

def check_record(r, root):
    for field in ("id","original_author","source_url","source_file","sha256",
                  "review_receipt","extractor_receipt","reviewed_span","country_iso3",
                  "commitment_id","study_id","observation_start","observation_end",
                  "metric","unit","value","evidence_class"):
        require(field in r, "missing field: "+field)
    require(r["evidence_class"] == "original_observation", "unreviewed or inferred evidence")
    require(r["study_id"] in STUDIES, "unknown study")
    require(r["metric"] in METRICS, "unknown metric")
    require(isinstance(r["country_iso3"],str) and len(r["country_iso3"])==3
            and r["country_iso3"].isupper() and r["country_iso3"].isalpha(), "invalid country code")
    require(isinstance(r["source_url"],str) and r["source_url"].startswith("https://"), "source URL")
    require(isinstance(r["review_receipt"],str) and bool(r["review_receipt"].strip()), "missing independent review")
    require(isinstance(r["extractor_receipt"],str) and bool(r["extractor_receipt"].strip()), "missing extraction provenance")
    require(isinstance(r["reviewed_span"],str) and bool(r["reviewed_span"].strip()), "empty reviewed span")
    require(isinstance(r["original_author"],str) and bool(r["original_author"].strip()), "missing original author")
    require(isinstance(r["commitment_id"],str) and bool(r["commitment_id"].strip()), "missing commitment ID")
    require(r["observation_start"] <= r["observation_end"]
            and len(r["observation_start"])==10 and len(r["observation_end"])==10, "bad interval")
    require(r.get("causal_attribution") is None, "causal promotion forbidden")
    require(r.get("measured_emissions_effect_of_campaign") is None, "campaign effect promotion forbidden")
    require(r["metric"] != "compliance_score" or r["unit"] == "G20RG_-1_to_1", "compliance scale mismatch")
    require(r["metric"] != "emissions" or r["unit"] in {"MtCO2e","tCO2e"}, "emissions units")
    require(r["metric"] != "finance" or r["unit"] in {"USD_nominal","USD_2020"}, "finance units")
    require(r["metric"] != "ndc_procedural" or r["unit"] == "binary_recorded_procedure", "NDC unit mismatch")
    require(isinstance(r["value"], (int,float)) and not isinstance(r["value"],bool), "non-numeric value")
    if r["metric"]=="compliance_score":
        require(-1 <= r["value"] <= 1, "compliance score outside original scale")
    path = safe_path(root,r["source_file"])
    raw = path.read_bytes()
    require(hashlib.sha256(raw).hexdigest()==r["sha256"], "source digest mismatch")
    # Exact UTF-8 text is accepted for passage matching. Binary/PDF requires
    # separate extraction with independent provenance; it cannot silently pass.
    require(path.suffix.lower() in {".txt",".html",".htm"}, "binary source needs reviewed text extraction")
    decoded = raw.decode("utf-8")
    require(r["reviewed_span"] in decoded, "reviewed passage absent from source")
    return (r["study_id"],r["country_iso3"],r["commitment_id"],r["metric"],r["unit"],
            r["observation_start"],r["observation_end"])

def validate(data, root):
    require(data.get("schema")==SCHEMA, "wrong schema")
    records=data.get("records")
    require(isinstance(records,list), "records missing")
    ids=set(); keys=set()
    for r in records:
        require(r["id"] not in ids, "duplicate record id")
        ids.add(r["id"])
        key=check_record(r,root)
        require(key not in keys, "duplicate observation")
        keys.add(key)
    return {"admitted_original_records":len(records),
            "country_outcome_panel_complete":False if not records else None,
            "cross_report_harmonization_proved":False,
            "causal_effect_identified":False}

def self_test():
    import tempfile
    with tempfile.TemporaryDirectory() as directory:
        root=Path(directory); (root/"evidence.txt").write_text("Observed country action",encoding="utf-8")
        sample={"id":"SYNTHETIC","original_author":"Fixture author",
                "source_url":"https://example.org/fixture","source_file":"evidence.txt",
                "sha256":hashlib.sha256((root/"evidence.txt").read_bytes()).hexdigest(),
                "review_receipt":"fixture review only","extractor_receipt":"fixture extractor",
                "reviewed_span":"Observed country action","country_iso3":"AUS",
                "commitment_id":"fixture-commitment","study_id":"brisbane2014_final_G20RG",
                "observation_start":"2014-11-16","observation_end":"2015-10-01",
                "metric":"compliance_score","unit":"G20RG_-1_to_1","value":0.5,
                "evidence_class":"original_observation","causal_attribution":None,
                "measured_emissions_effect_of_campaign":None}
        data={"schema":SCHEMA,"records":[sample]}
        require(validate(data,root)["admitted_original_records"]==1, "positive synthetic control")
        for field,bad in (("sha256","0"*64),("reviewed_span","absent"),("unit","percent"),
                          ("evidence_class","inferred"),("causal_attribution","GCC caused outcome"),
                          ("country_iso3","australia")):
            changed=dict(sample);changed[field]=bad
            try: validate({"schema":SCHEMA,"records":[changed]},root)
            except ValueError: pass
            else: raise AssertionError("negative control accepted: "+field)
        for bad in ("../evidence.txt","/etc/passwd"):
            changed=dict(sample); changed["source_file"]=bad
            try: validate({"schema":SCHEMA,"records":[changed]},root)
            except ValueError: pass
            else: raise AssertionError("path escape accepted")
        try: validate({"schema":SCHEMA,"records":[sample,sample]},root)
        except ValueError: pass
        else: raise AssertionError("duplicate accepted")
    return {"synthetic_positive":1,"synthetic_negative":9,"real_country_records_verified":0}

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument("--input",type=Path)
    parser.add_argument("--source-root",type=Path)
    parser.add_argument("--self-test",action="store_true")
    args=parser.parse_args()
    if args.self_test:
        print(json.dumps(self_test(),sort_keys=True));return
    require(args.input is not None and args.source_root is not None, "provide --input and --source-root")
    data=json.loads(args.input.read_text(encoding="utf-8"))
    result=validate(data,args.source_root)
    require(result["admitted_original_records"]>0, "no original observations admitted")
    print(json.dumps(result,sort_keys=True))

if __name__=="__main__":
    main()
