#!/usr/bin/env python3
"""P0 direct official MMS Science Data Center acquisition (no PySPEDAS needed).

Original SDC API:
 https://lasp.colorado.edu/mms/sdc/public/about/how-to/
 - /files/api/v1/file_names/science?sc_id=mms1&start_date=2017-06-17&
     end_date=2017-06-18&data_rate_mode=brst&data_level=l2
 - /files/api/v1/download/science?file=<EXACT SDC RETURNED FILENAME>

The exact event under study is 2017-06-17T20:24:03..20:24:11 UTC.
Only filenames actually returned by the official service are considered.
Original filename timestamps DO NOT imply the event was sampled: CDF Epoch
values MUST be audited after download. The script fails closed if data do
not cover the original event in each of all four required L2 instruments.

Default mode is offline plan. --execute requires network and cdflib; the
program never emits fake source hashes. Re-run with --verify to audit exact
bytes and epoch ranges from a previous manifest. Downloading CDFs is not
an instrument calibration or determination of the original author's J·E'.
"""
from __future__ import annotations
import argparse,hashlib,json,re
from datetime import datetime,timedelta,timezone
from pathlib import Path
from urllib.parse import urlencode
from urllib.request import Request,urlopen
from urllib.error import HTTPError,URLError

ROOT="https://lasp.colorado.edu/mms/sdc/public/files/api/v1"
DATE="2017-06-17"
EVENT_START=datetime(2017,6,17,20,24,3,tzinfo=timezone.utc)
EVENT_END=datetime(2017,6,17,20,24,11,tzinfo=timezone.utc)
SPECS={
 "fgm":r"^mms1_fgm_brst_l2_(\d{14})_v(\d+\.\d+\.\d+)\.cdf$",
 "edp":r"^mms1_edp_brst_l2_dce_(\d{14})_v(\d+\.\d+\.\d+)\.cdf$",
 "des":r"^mms1_fpi_brst_l2_des-moms_(\d{14})_v(\d+\.\d+\.\d+)\.cdf$",
 "dis":r"^mms1_fpi_brst_l2_dis-moms_(\d{14})_v(\d+\.\d+\.\d+)\.cdf$",
}


def sha256(path):
    h=hashlib.sha256()
    with Path(path).open("rb") as f:
        for c in iter(lambda:f.read(1<<20),b""):h.update(c)
    return h.hexdigest()


def make_listing_url():
    return ROOT+"/file_names/science?"+urlencode({
      "sc_id":"mms1",
      "start_date":DATE,
      "end_date":"2017-06-18",
      "data_rate_mode":"brst",
      "data_level":"l2",
    })


def parse_original_names(body:bytes):
    data=body.decode("utf-8-sig").strip()
    if data[:1] in ("<","{","["):
        raise ValueError("Expected MMS SDC comma-separated filename listing")
    names=[x.strip().strip('"').strip("'") for x in re.split("[,\r\n]+",data)]
    names=[x for x in names if x]
    if any("/" in x or ".." in x for x in names):
        raise ValueError("Unexpected path in original source file names")
    return names


def select_near_event(names,lookback_minutes=10):
    if not (0<lookback_minutes<=60):raise ValueError("Invalid bounded burst lookback")
    lo=EVENT_START-timedelta(minutes=lookback_minutes)
    hi=EVENT_END
    matches={}
    for product,pattern in SPECS.items():
        candidate={}
        for name in names:
            match=re.match(pattern,name.lower())
            if not match:continue
            start=datetime.strptime(match.group(1),"%Y%m%d%H%M%S").replace(
                tzinfo=timezone.utc)
            if not lo<=start<=hi:continue
            version=tuple(map(int,match.group(2).split(".")))
            prior=candidate.get(start)
            if prior is None or version>prior[0]:
                candidate[start]=(version,name)
        if not candidate:
            raise ValueError(f"No official SDC {product} burst file begins in bounded window")
        matches[product]=[{"filename":v[1],"start_utc":k.isoformat(),
                           "version":v[0]} for k,v in sorted(candidate.items())]
    return matches


def metadata_epoch_overlap(path):
    """Audit actual times from Epoch of source L2 FGM/EDP/FPI CDF.

    Source includes burst data for a time interval; the returned file name
    timestamp is NOT sufficient evidence for actual overlapping samples.
    """
    import numpy as np
    from cdflib import CDF,cdfepoch
    c=CDF(str(path))
    try:
        vars_=c.cdf_info().zVariables
        if "Epoch" not in vars_:
            # FGM/EDP CDFs can name their epoch variable differently.
            epochs=[v for v in vars_ if re.search("epoch",v,re.I)]
            if len(epochs)!=1:
                raise ValueError(f"ambiguous CDF epoch variables: {epochs}")
            var=epochs[0]
        else:var="Epoch"
        raw=c.varget(var)
        times=np.asarray(cdfepoch.to_datetime(raw),dtype="datetime64[ns]")
        if not len(times):raise ValueError("Empty source CDF Epoch")
        t0=np.datetime64(EVENT_START.replace(tzinfo=None),"ns")
        t1=np.datetime64(EVENT_END.replace(tzinfo=None),"ns")
        good=(times>=t0)&(times<t1)
        return {
            "cdf_epoch_var":var,"cdf_total_epochs":int(len(times)),
            "cdf_event_samples":int(good.sum()),
            "cdf_min_utc":str(times.min()),
            "cdf_max_utc":str(times.max()),
            "actual_original_event_overlap":bool(good.any()),
        }
    finally:c.close()


def original_download(name,target,max_file_mb=256):
    url=ROOT+"/download/science?"+urlencode({"file":name})
    req=Request(url,headers={"User-Agent":"DASHI-KSW668-MMS-raw-archive/1.0"})
    target=Path(target)
    tmp=target.with_suffix(".part")
    max_bytes=max_file_mb*(1<<20)
    written=0
    with urlopen(req,timeout=120) as resp, tmp.open("wb") as sink:
        if "text/html" in resp.headers.get("Content-Type","").lower():
            raise ValueError("Official SDC returned HTML rather than CDF: "+name)
        for chunk in iter(lambda:resp.read(1<<20),b""):
            written+=len(chunk)
            if written>max_bytes:
                tmp.unlink(missing_ok=True)
                raise ValueError("CDF exceeded explicit byte limit")
            sink.write(chunk)
    if written<256:
        tmp.unlink(missing_ok=True)
        raise ValueError("Invalid or too-small CDF")
    tmp.replace(target)
    return {"relative_path":name,"sha256":sha256(target),"bytes":written,
            "exact_archive_url":url}


def execute(cache,lookback_minutes=10,max_mb=256):
    req=Request(make_listing_url(),headers={"User-Agent":"DASHI-KSW668-MMS/1.0"})
    with urlopen(req,timeout=60) as resp:
        listing=resp.read(4<<20)
    filename_list=parse_original_names(listing)
    selected=select_near_event(filename_list,lookback_minutes)
    cache=Path(cache);cache.mkdir(parents=True,exist_ok=True)
    acquired={};all_cdfs=[]
    for product,available in selected.items():
        actual=[]
        for item in available:
            row=original_download(item["filename"],cache/item["filename"],max_mb)
            row.update(metadata_epoch_overlap(cache/item["filename"]))
            actual.append(row);all_cdfs.append(row)
        if not any(x["actual_original_event_overlap"] for x in actual):
            raise ValueError(f"SDC {product} burst did not sample actual original event")
        acquired[product]=actual
    return {
      "schema":"dashi.ksw668.mms-official-sdc-direct-v1",
      "source_api_listing_url":make_listing_url(),
      "source_listing_sha256":hashlib.sha256(listing).hexdigest(),
      "spacecraft":"MMS1",
      "event_UTC":{"start":"2017-06-17/20:24:03","end":"2017-06-17/20:24:11"},
      "event_papers":["10.1029/2020GL088761","10.1029/2022GL098445"],
      "download_source":"official unauthenticated LASP MMS SDC API",
      "per_product_event_covered":{k:any(a["actual_original_event_overlap"]
                    for a in v) for k,v in acquired.items()},
      "cdf_files":all_cdfs,
      "instrument_synchronization_and_quality_accepted":False,
      "not_established":"actual J.Eprime physics, uncertainty, LMN and source-original currents",
    }


def verify(cache,receipt):
    r=json.loads(Path(receipt).read_text(encoding="utf-8"))
    if r["spacecraft"]!="MMS1":raise ValueError("Unrelated spacecraft")
    if not r["cdf_files"]:raise ValueError("Empty CDF receipt")
    for item in r["cdf_files"]:
        rel=Path(item["relative_path"])
        if rel.is_absolute() or ".." in rel.parts:raise ValueError("Invalid path")
        f=Path(cache)/rel
        if not f.is_file() or sha256(f)!=item["sha256"]:
            raise ValueError("Original SHA mismatch: "+str(f))
        epoch=metadata_epoch_overlap(f)
        if epoch["cdf_event_samples"]!=item["cdf_event_samples"]:
            raise ValueError("CDF epoch overlap has changed")
    if not all(r["per_product_event_covered"].values()):
        raise ValueError("Missing some event source products")
    return {"verified":len(r["cdf_files"]),"original_event_covered":True}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--cache",type=Path,default=Path("data/mms_original_SDC_20170617"))
    ap.add_argument("--execute",action="store_true")
    ap.add_argument("--verify",type=Path)
    ap.add_argument("--receipt",type=Path)
    ap.add_argument("--lookback-minutes",type=int,default=10)
    ap.add_argument("--max-file-mb",type=int,default=256)
    args=ap.parse_args()
    if args.execute:
        if args.receipt is None:ap.error("--execute requires --receipt")
        result=execute(args.cache,args.lookback_minutes,args.max_file_mb)
        args.receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    elif args.verify:
        result=verify(args.cache,args.verify)
    else:
        result={"status":"plan-only; original CDF bytes NOT retrieved",
                "official_listing_api":make_listing_url(),
                "event_utc":["2017-06-17T20:24:03Z","2017-06-17T20:24:11Z"],
                "next":"--execute --receipt /tmp/mms_sdc_original_sha.json"}
    print(json.dumps(result,indent=2))


if __name__=="__main__":main()
