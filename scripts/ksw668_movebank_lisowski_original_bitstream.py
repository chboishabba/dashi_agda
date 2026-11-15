#!/usr/bin/env python3
"""E1 original Lisowski et al. Movebank GPS CDF-equivalent provenance gate.

Original source: Movebank repository package DOI 10.5441/001/1.744_2,
UUID 2f38f106-42bf-4c4a-b7a4-17d758bdd9a9, 2026 Science
DOI 10.1126/science.ady2486.
Independent *secondary* verification: zuizui0223/RSDS,
research/GLOBAL_SOLAR_AZIMUTH_NEW24_ORIGINAL_GPS_FIRST_V2_RESULT_20261025.json
and research/GLOBAL_SOLAR_AZIMUTH_NEW24_PROVIDER_FROZEN_SOURCE_FILE_MANIFEST_20261025.json.
Reports original bitstream UUID b36da51a-30d5-4e4a-856c-940d7b9c27e3,
original file 705,083 bytes, provider MD5
420dd8de4e0afe50f78ac848846591ba, 4,347 GPS rows / 34 birds,
archive licence Attribution-NonCommercial 4.0 International.

The script does not pretend another project's original-provider MD5 is
equivalent to downloading and re-verifying original bytes here.
--execute downloads from the DSpace public bitstream REST resource;
--input independently verifies a user-acquired ORIGINAL Movebank CSV.
Do not infer experimental treatment from 34 source birds or counts alone.
"""
import argparse,csv,hashlib,io,json
from pathlib import Path
from urllib.request import Request,urlopen

DOI="10.5441/001/1.744_2"
PAPER="10.1126/science.ady2486"
PACKAGE="2f38f106-42bf-4c4a-b7a4-17d758bdd9a9"
BITSTREAM="b36da51a-30d5-4e4a-856c-940d7b9c27e3"
DIRECT="https://datarepository.movebank.org/server/api/core/bitstreams/"+BITSTREAM+"/content"
ORIGINAL_MD5="420dd8de4e0afe50f78ac848846591ba"
ORIGINAL_BYTES=705083
SOURCE_ROWS=4347
SOURCE_BIRDS=34

def verify(data):
    if len(data)!=ORIGINAL_BYTES:raise ValueError("Original Lisowski GPS byte length mismatch")
    if hashlib.md5(data).hexdigest()!=ORIGINAL_MD5:
        raise ValueError("Original Movebank/provider MD5 mismatch")
    if data[:30].lstrip().lower().startswith((b"<html",b"<!doctype html")):
        raise ValueError("Not original GPS CSV")
    text=data.decode("utf-8-sig")
    original=list(csv.DictReader(io.StringIO(text)))
    if len(original)!=SOURCE_ROWS:
        raise ValueError("Third-party original source row count differs from actual CSV")
    cols=set(original[0]) if original else set()
    id_cols=["individual-local-identifier","individual-local-identifier.1",
             "individual-id","tag-local-identifier"]
    idfield=next((c for c in id_cols if c in cols),None)
    identities=len({r[idfield] for r in original if r[idfield].strip()}) if idfield else None
    if identities is not None and identities!=SOURCE_BIRDS:
        raise ValueError("Original source bird census differs from independent audit")
    return {
      "status":"PASS original data MD5 + size + 4347 rows; SHA256 locally computed",
      "movebank_package":PACKAGE,"dataset_doi":DOI,"study_paper_doi":PAPER,
      "bitstream_uuid":BITSTREAM,
      "original_file_bytes":len(data),"original_provider_MD5":ORIGINAL_MD5,
      "original_source_sha256":hashlib.sha256(data).hexdigest(),
      "source_location_rows":len(original),"bird_id_column":idfield,
      "distinct_birds_if_column_present":identities,
      "original_columns":list(original[0]),
      "provider_original_source_version":"DSpace original bitstream UUID, not downloadable HTML",
      "original_data_license":"CC BY-NC 4.0",
      "treatment_sidecar_join_complete":False,
      "published_16_control_0_depleted_outcome_reproduced":False,
    }

def download():
    req=Request(DIRECT,headers={"User-Agent":"DASHI-KSW668-Primary/1.0"})
    with urlopen(req,timeout=120) as r:
        typ=r.headers.get("Content-Type","").lower()
        if "text/html" in typ:raise ValueError("Movebank returned HTML, not data")
        data=r.read(ORIGINAL_BYTES+1)
    return data

def main():
    p=argparse.ArgumentParser(description=__doc__)
    group=p.add_mutually_exclusive_group()
    group.add_argument("--execute",action="store_true")
    group.add_argument("--input",type=Path)
    p.add_argument("--out",type=Path)
    p.add_argument("--receipt",type=Path)
    a=p.parse_args()
    if a.execute:
        if a.out is None:p.error("--execute requires --out")
        raw=download()
        result=verify(raw)
        a.out.parent.mkdir(parents=True,exist_ok=True)
        a.out.write_bytes(raw)
    elif a.input:
        result=verify(a.input.read_bytes())
    else:
        result={"status":"SOURCE METADATA ONLY; original bytes not acquired",
                "direct_original_content_endpoint":DIRECT,
                "independent_original_provider_verified_MD5":ORIGINAL_MD5,
                "expected_original_bytes":ORIGINAL_BYTES,
                "expected_original_GPS_rows":SOURCE_ROWS,
                "expected_original_birds":SOURCE_BIRDS,
                "original_dataset_license":"CC BY-NC 4.0",
                "next":"--execute --out /path/to/original_movebank_pigeons.csv"}
    if a.receipt:a.receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+"\n")
    print(json.dumps(result,indent=2))

if __name__=="__main__":
    main()
