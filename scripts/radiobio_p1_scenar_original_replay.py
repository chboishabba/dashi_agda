#!/usr/bin/env python3
"""Participant-level SCENAR active/sham audit from an explicitly mapped CSV.

Original experiment: Michel-Cherqui et al., Journal of Clinical Medicine 2021,
doi:10.3390/jcm10235570; trial NCT03755817.
Original data: Fischler, Dryad doi:10.5061/dryad.63xsj3v2s,
filename Scenar_-_Dryad_Corrigé.xlsx (21.86 KB). Original researcher owns data.

This tool NEVER guesses source workbook column names or fabricates participants.
The original XLSX must first be acquired and validated; investigator maps its
actual columns to CSV with: participant_id,arm,rest_before,rest_after,rest_24h.
The script cannot reproduce the paper's SAS mixed-model p-value from medians.
No original patient data should ever be committed to the source repository.
"""
import argparse
import csv
import hashlib
import json
import math
from pathlib import Path
from statistics import mean

ARMS=("on","off")
FIELDS=("participant_id","arm","rest_before","rest_after","rest_24h")


def sha256(path):
    h=hashlib.sha256()
    with open(path,"rb") as fh:
        for block in iter(lambda:fh.read(1024*1024),b""):
            h.update(block)
    return h.hexdigest()


def parse_rows(path, require_complete=True):
    with open(path,encoding="utf-8-sig",newline="") as fh:
        reader=csv.DictReader(fh)
        if not reader.fieldnames or any(field not in reader.fieldnames for field in FIELDS):
            raise ValueError("explicit five-column source mapping is required")
        rows=list(reader)
    if not rows:
        raise ValueError("empty source")
    seen=set()
    result=[]
    for i,row in enumerate(rows,2):
        pid=row["participant_id"].strip()
        arm=row["arm"].strip().lower()
        if not pid or pid in seen:
            raise ValueError("missing/duplicate participant identifier at row "+str(i))
        seen.add(pid)
        if arm not in ARMS:
            raise ValueError("source arm needs explicit on/off mapping")
        vals=[]
        for name in FIELDS[2:]:
            try:
                v=float(row[name])
            except (TypeError,ValueError):
                raise ValueError("non-numeric observation "+name+" row "+str(i))
            if not math.isfinite(v) or v<0 or v>10:
                raise ValueError("pain NRS must be finite on original 0..10 scale")
            vals.append(v)
        result.append((pid,arm,*vals))
    byarm={arm:[r for r in result if r[1]==arm] for arm in ARMS}
    if any(len(byarm[a])==0 for a in ARMS):
        raise ValueError("both active and sham arms must contain participants")
    if require_complete and (len(result)!=60 or any(len(byarm[a])!=30 for a in ARMS)):
        raise ValueError("not the reported complete 60-person / 30-per-arm trial; explicitly review missingness")
    return result,byarm


def summarize(path,expected_sha256=None,require_complete=True):
    actual=sha256(path)
    if expected_sha256 and actual.lower()!=expected_sha256.lower():
        raise ValueError("source CSV SHA256 differs from supplied local chain-of-custody manifest")
    rows,byarm=parse_rows(path,require_complete)
    summary={}
    for arm in ARMS:
        vals=byarm[arm]
        change=[r[3]-r[2] for r in vals]
        delayed=[r[4]-r[2] for r in vals]
        summary[arm]={
            "n":len(vals),"baseline_mean":mean(r[2] for r in vals),
            "immediate_mean":mean(r[3] for r in vals),
            "mean_immediate_change":mean(change),
            "mean_24h_change":mean(delayed)}
    contrast=summary["on"]["mean_immediate_change"]-summary["off"]["mean_immediate_change"]
    return {"status":"ANALYZED_USER_MAPPED_CSV_NOT_ORIGINAL_SAS_MIXED_MODEL",
            "sha256_mapped_csv":actual,
            "original_xlsx_SHA256_verified":False,
            "original_trial_registry":"NCT03755817",
            "original_data_doi":"10.5061/dryad.63xsj3v2s",
            "n":len(rows),"arms":summary,
            "difference_of_mean_changes_on_minus_off":contrast,
            "published_between_group_p_at_rest":0.22,
            "reproduced_published_mixed_model":False,
            "caution":"Unadjusted means; not source's original repeated-measures mixed model or its inferential test."}


def self_test():
    import tempfile
    with tempfile.TemporaryDirectory() as tmp:
        path=Path(tmp)/"synthetic.csv"
        with path.open("w",encoding="utf8",newline="") as fh:
            w=csv.writer(fh)
            w.writerow(FIELDS)
            for arm in ARMS:
                for i in range(30):
                    w.writerow([arm+str(i),arm,8,5,8])
        result=summarize(path)
        assert result["n"]==60
        assert result["difference_of_mean_changes_on_minus_off"]==0
        assert result["original_xlsx_SHA256_verified"] is False
        bad=Path(tmp)/"bad.csv"
        bad.write_text("participant_id,arm,rest_before,rest_after,rest_24h\n"
                       "same,on,8,5,8\nsame,off,8,5,8\n")
        try:
            parse_rows(bad,require_complete=False)
            raise AssertionError("duplicate control bypassed")
        except ValueError as e:
            assert "duplicate" in str(e)
        try:
            summarize(path,expected_sha256="0"*64)
            raise AssertionError("checksum guard bypassed")
        except ValueError as e:
            assert "SHA256" in str(e)
        one_arm=Path(tmp)/"one_arm.csv"
        one_arm.write_text("participant_id,arm,rest_before,rest_after,rest_24h\\n"
                           "synthetic1,on,8,5,8\\n")
        try:
            summarize(one_arm,require_complete=False)
            raise AssertionError("empty sham arm bypassed")
        except ValueError as e:
            assert "both active and sham" in str(e)
    return {"status":"PASS","synthetic_tests":6,"source_XLSX_loaded":False,
            "original_patient_data_reproduced":False}


def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--mapped-csv",type=Path)
    p.add_argument("--expected-csv-sha256")
    p.add_argument("--allow-incomplete",action="store_true")
    p.add_argument("--receipt",type=Path)
    args=p.parse_args()
    result=(summarize(args.mapped_csv,args.expected_csv_sha256,not args.allow_incomplete)
            if args.mapped_csv else self_test())
    output=json.dumps(result,indent=2,sort_keys=True)+"\n"
    print(output)
    if args.receipt:
        args.receipt.parent.mkdir(parents=True,exist_ok=True)
        args.receipt.write_text(output,encoding="utf8")


if __name__=="__main__":
    main()
