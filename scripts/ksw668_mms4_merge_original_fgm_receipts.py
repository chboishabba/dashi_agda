#!/usr/bin/env python3
"""P0/B2 four ORIGINAL MMS FGM receipts -> raw source ephemeris manifest.

Usage after original MMS per-probe SDC downloads:
  python scripts/ksw668_mms_sdc_direct.py --probe 1 --products fgm \
    --cache /data/mms4 --execute --receipt /data/receipts/mms1.json
  ... similarly probes 2,3,4 ...
  python scripts/ksw668_mms4_merge_original_fgm_receipts.py \
    --cache /data/mms4 --receipts /data/receipts/mms{1,2,3,4}.json \
    --out /data/receipts/mms4_fgm_source.json

This joins only actual downloaded FGM source files with proper original
MMS dates/spacecraft, positive 2017 event overlap, SHA256 over the raw
CDF BYTES and provenance from the official public SDC listing receipts.
Does not accept a manifest or filenames as source measurements, invent
unmeasured E/B/J, or claim independent source-origin cryptographic proof.
"""
import argparse,hashlib,json,re
from pathlib import Path

EXPECTED_EVENT={"start":"2017-06-17/20:24:03","end":"2017-06-17/20:24:11"}
NAME=re.compile(r"^(mms[1-4])_fgm_brst_l2_20170617\d{6}_v\d+\.\d+\.\d+\.cdf$",re.I)

def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for b in iter(lambda:f.read(1<<20),b""):h.update(b)
    return h.hexdigest()

def merge(cache,receipts):
    if len(receipts)!=4:raise ValueError("Must supply exactly four separate original SDC probe receipts")
    cache=Path(cache)
    result={}
    for receipt in receipts:
        obj=json.loads(Path(receipt).read_text(encoding="utf-8"))
        spacecraft=obj.get("spacecraft","").lower()
        if spacecraft not in ("mms1","mms2","mms3","mms4") or spacecraft in result:
            raise ValueError("Wrong or repeated MMS original spacecraft")
        if obj.get("schema")!="dashi.ksw668.mms-official-sdc-direct-v1" or obj.get("event_UTC")!=EXPECTED_EVENT:
            raise ValueError("Unrecognized original SDC event receipt")
        if obj.get("per_product_event_covered",{}).get("fgm") is not True:
            raise ValueError("Original FGM burst data did not cover selected event")
        source_url=obj.get("source_api_listing_url","")
        if not source_url.startswith("https://lasp.colorado.edu/mms/sdc/public/files/api/v1/file_names/science?"):
            raise ValueError("Missing official SDC file-listing URL")
        if "sc_id="+spacecraft not in source_url:
            raise ValueError("SDC source listing not for expected spacecraft")
        entries=[]
        for info in obj.get("cdf_files",[]):
            filename=info.get("relative_path","")
            m=NAME.fullmatch(filename)
            if not m or m.group(1).lower()!=spacecraft:
                continue
            if info.get("cdf_event_samples",0)<=0 or info.get("actual_original_event_overlap") is not True:
                continue
            path=cache/filename
            digest=info.get("sha256","")
            if not path.is_file() or not re.fullmatch("[0-9a-f]{64}",digest):
                raise ValueError("Original source file unreadable or digest absent")
            if sha256(path)!=digest:
                raise ValueError("Original FGM CDF SHA mismatch")
            entries.append({"spacecraft":spacecraft,"path":str(path.resolve()),
                            "sha256":digest,"original_event_samples":info["cdf_event_samples"],
                            "source_listing_sha256":obj.get("source_listing_sha256")})
        if not entries:raise ValueError("No original source FGM CDF covers event for "+spacecraft)
        # Files can overlap a burst boundary; for the 2 selected internal
        # epochs one original file covering the entire interval is ideal,
        # but positive event sample count is NOT that guarantee. Downstream
        # Epoch_state and field validation must confirm both query times.
        selected=max(entries,key=lambda z:z["original_event_samples"])
        result[spacecraft]=selected
    return {
      "schema":"dashi.ksw668.mms4-original-fgm-ephemeris-input.v1",
      "date_utc":"2017-06-17",
      "source":"LASP MMS SDC official public file_names/download science API",
      "files":[{k:result[s][k] for k in ("spacecraft","path","sha256")}
               for s in ("mms1","mms2","mms3","mms4")],
      "original_source_receipt_files":[str(Path(r)) for r in receipts],
      "per_probe_source_listing_sha256":{s:result[s]["source_listing_sha256"] for s in result},
      "per_probe_source_event_samples":{s:result[s]["original_event_samples"] for s in result},
      "source_CDF_contents_SHA256_reverified":True,
      "two_event_query_times_original_FGM_field_bracket_verified":False,
      "original_FGM_ephemeris_position_bracket_verified":False,
      "independent_external_signature_of_SDC_origin":False,
      "physical_measured_3D_Poynting_boundary":False
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument("--cache",type=Path,required=True)
    p.add_argument("--receipts",nargs=4,type=Path,required=True)
    p.add_argument("--out",type=Path,required=True)
    ns=p.parse_args()
    obj=merge(ns.cache,ns.receipts)
    ns.out.parent.mkdir(parents=True,exist_ok=True)
    ns.out.write_text(json.dumps(obj,sort_keys=True,indent=2)+"\n")
    print(json.dumps(obj,indent=2))

if __name__=="__main__":
    main()
