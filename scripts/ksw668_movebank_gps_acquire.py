#!/usr/bin/env python3
"""Movebank Lisowski pigeon-GPS acquisition with first-class source provenance.

User-supplied candidate accession: DOI 10.5441/001/1.744_2; dataset landing:
https://datarepository.movebank.org/entities/datapackage/2f38f106-42bf-4c4a-b7a4-17d758bdd9a9

No archive bitstream/sha/individual labels were independently validated by
this authoring run. Supply the ORIGINAL downloaded file (--input) or the
verified direct URL from the repository's Download control (--url).
Never invent an item download URL, use HTML as CSV, or infer treatment from an
anonymous animal ID. Movebank's license and the source paper apply.

This tool reconstructs (a) raw checksums (b) schema and time/coordinate bounds
(c) per-animal fix counts. It cannot claim trajectory-derived homing success
until the original reference/treatment and loft location are joined.
"""
import argparse, csv, hashlib, io, json, zipfile
from collections import Counter
from datetime import datetime
from pathlib import Path
from urllib.request import Request, urlopen
from urllib.parse import urlparse

DOI="10.5441/001/1.744_2"
LANDING=("https://datarepository.movebank.org/entities/datapackage/"
         "2f38f106-42bf-4c4a-b7a4-17d758bdd9a9")
PREFERRED="Navigation with macrophage depletion in homing pigeons.csv"


def digest(data):
    return hashlib.sha256(data).hexdigest()


def get_bytes(args):
    if args.input:
        raw=Path(args.input).read_bytes()
        url=None
    else:
        parsed=urlparse(args.url)
        if parsed.scheme!="https" or not (parsed.hostname=="datarepository.movebank.org"
                                            or parsed.hostname.endswith(".movebank.org")):
            raise ValueError("Direct download must be an HTTPS Movebank host")
        req=Request(args.url,headers={"User-Agent":"DASHI-KSW668-primary-audit/1.0"})
        with urlopen(req,timeout=60) as r:
            if ("text/html" in r.headers.get("Content-Type","").lower()):
                raise ValueError("Got landing-page HTML instead of original data")
            raw=r.read(100*1024*1024+1)
        if len(raw)>100*1024*1024: raise ValueError("Oversize download; use original local file")
        url=args.url
    if args.expected_sha256 and digest(raw).lower()!=args.expected_sha256.lower():
        raise ValueError("Original payload SHA-256 mismatch")
    if len(raw)<20:raise ValueError("Invalid or truncated Movebank payload")
    return raw,url


def read_csv(raw):
    text=raw.decode("utf-8-sig")
    if "<html" in text[:200].lower(): raise ValueError("HTML is not GPS CSV")
    reader=csv.DictReader(io.StringIO(text))
    fields=reader.fieldnames or []
    if not fields:raise ValueError("No header")
    return fields,list(reader)


def unpackage(raw):
    if raw[:2]==b"PK":
        with zipfile.ZipFile(io.BytesIO(raw)) as z:
            names=[n for n in z.namelist() if n.lower().endswith(".csv")
                   and not n.startswith("__MACOSX/")]
            matched=[n for n in names if Path(n).name.lower()==PREFERRED.lower()]
            if len(matched)!=1:
                raise ValueError("Ambiguous archive. Expected exact GPS CSV name; "
                                 "found "+str(names))
            item=matched[0]
            return z.read(item),item,z.read("README.txt").decode(errors="replace")[:1200] \
                    if "README.txt" in z.namelist() else None
    return raw,PREFERRED,None


def find_col(fields,*candidates):
    canonical={s.lower().strip().replace("_","-").replace(" ","-"):s for s in fields}
    for name in candidates:
        result=canonical.get(name.lower().replace("_","-").replace(" ","-"))
        if result:return result
    return None


def validate_gps(data):
    fields,rows=read_csv(data)
    id_key=find_col(fields,"individual-local-identifier","individual local identifier",
                    "individual-id","animal-id","individual-taxon-canonical-name")
    lat_key=find_col(fields,"location-lat","location-latitude","latitude")
    lon_key=find_col(fields,"location-long","location-longitude","longitude")
    t_key=find_col(fields,"timestamp","event-timestamp","time")
    if not all((id_key,lat_key,lon_key,t_key)):
        raise ValueError("Original schema lacks id/time/latitude/longitude; columns: "
                         + repr(fields))
    counts=Counter()
    minmax={}
    ncoord=0
    for row in rows:
        ident=row[id_key].strip()
        if not ident:continue
        lat,lon=row[lat_key].strip(),row[lon_key].strip()
        if lat and lon:
            la,lo=float(lat),float(lon)
            if not (-90<=la<=90 and -180<=lo<=180):
                raise ValueError("Invalid geographic coordinates")
            ncoord+=1
        tm=row[t_key].strip()
        if not tm:continue
        counts[ident]+=1
        if ident not in minmax:minmax[ident]=[tm,tm]
        else:
            minmax[ident][0]=min(minmax[ident][0],tm)
            minmax[ident][1]=max(minmax[ident][1],tm)
    if not ncoord or not counts:raise ValueError("No valid GPS fixes")
    return {"header":fields,"all_raw_rows":len(rows),"gps_fixes_with_coords":ncoord,
            "animals_in_file":len(counts),
            "records_by_individual":dict(sorted(counts.items())),
            "timestamp_bounds_lexical":dict(sorted(minmax.items())),
            "treatment_join_present":False,
            "homing_endpoint_reconstructed":False}


def main():
    ap=argparse.ArgumentParser(description=__doc__)
    src=ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--input",help="Raw downloaded Movebank GPS CSV or ZIP")
    src.add_argument("--url",help="Verified original direct bitstream, NOT landing page")
    ap.add_argument("--expected-sha256",help="Previously pinned original payload digest")
    ap.add_argument("--receipt",type=Path)
    ns=ap.parse_args()
    raw,url=get_bytes(ns)
    csv_bytes,mname,readme=unpackage(raw)
    report=validate_gps(csv_bytes)
    receipt={
        "schema":"dashi.ksw668.movebank-raw.v1",
        "dataset_doi_user_supplied_unresolved_by_this_run":DOI,
        "landing_url":LANDING,"source_direct_url":url,
        "source_original_payload_sha256":digest(raw),
        "source_csv_sha256":digest(csv_bytes),
        "source_csv_member_name":mname,
        "source_readme_excerpt":readme,
        "source_license_checked_by_user":False,
        "record_source":"Lisowski et al., Science (2026), DOI 10.1126/science.ady2486",
        "gps_audit":report,
        "physical_claim_gate":"not a same-bird treatment/loft/meteorology/trajectory inference",
    }
    txt=json.dumps(receipt,indent=2,sort_keys=True)+"\n"
    if ns.receipt:ns.receipt.write_text(txt)
    print(txt)


if __name__=="__main__":
    main()
