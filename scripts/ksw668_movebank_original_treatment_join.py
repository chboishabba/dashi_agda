#!/usr/bin/env python3
"""E1 source-SHA-pinned pigeon GPS, treatment, weather and censoring join.

Original Lisowski et al. 2026 DOI 10.1126/science.ady2486.
Only actual original Movebank GPS and reference/trial metadata admitted.
NEVER infer non-homing from missing GPS fixes without explicit original
same-day tracking-complete metadata. Local time zone and predeclared loft
radius required; do not infer from original bird location timestamps.
"""
import argparse,csv,hashlib,json,math
from collections import defaultdict
from datetime import datetime,timezone
from pathlib import Path
from zoneinfo import ZoneInfo

def read_rows(path,source_sha):
    raw=Path(path).read_bytes();digest=hashlib.sha256(raw).hexdigest()
    if digest!=source_sha.lower():raise ValueError("Original SHA mismatch")
    rows=list(csv.DictReader(raw.decode("utf-8-sig").splitlines()))
    if not rows:raise ValueError("Original source has no rows")
    return rows,digest

def utc(value):
    d=datetime.fromisoformat(value.replace("Z","+00:00"))
    if d.tzinfo is None:raise ValueError("Original event timestamp missing timezone")
    return d.astimezone(timezone.utc)

def meters(lat1,lon1,lat2,lon2):
    unit=math.pi/180
    a=math.sin((lat2-lat1)*unit/2)**2
    a+=math.cos(lat1*unit)*math.cos(lat2*unit)*math.sin((lon2-lon1)*unit/2)**2
    return 2*6371008.8*math.asin(min(1,math.sqrt(a)))

def reconstruct(gps,metadata,tz,loft_radius_m):
    if not 0<loft_radius_m<10000:raise ValueError("Invalid preregistered loft radius")
    required_gps={"individual-local-identifier","timestamp",
                  "location-lat","location-long"}
    required_meta={"individual-local-identifier","treatment",
                   "release_timestamp_utc","loft_lat","loft_lon",
                   "session_id","overcast","same_day_tracking_complete"}
    if not required_gps<=gps[0].keys() or not required_meta<=metadata[0].keys():
        raise ValueError("Original GPS/reference metadata lacks required columns")
    original={};tracks=defaultdict(list)
    for row in metadata:
        bird=row["individual-local-identifier"]
        if bird in original:raise ValueError("Duplicate original pigeon ID")
        if row["treatment"] not in ("control","macrophage_depleted"):
            raise ValueError("Unknown original treatment")
        if row["overcast"]!="true":raise ValueError("Not source overcast trial")
        if row["same_day_tracking_complete"] not in ("true","false"):
            raise ValueError("Tracking completeness cannot be inferred")
        row["release"]=utc(row["release_timestamp_utc"])
        original[bird]=row
    for row in gps:
        bird=row["individual-local-identifier"]
        if bird not in original:continue
        if not row["location-lat"] or not row["location-long"]:continue
        stamp=utc(row["timestamp"])
        la=float(row["location-lat"]);lo=float(row["location-long"])
        if not (-90<=la<=90 and -180<=lo<=180):
            raise ValueError("Invalid source coordinates")
        tracks[bird].append((stamp,la,lo))
    local_zone=ZoneInfo(tz);joined=[]
    for bird,row in original.items():
        release=row["release"]
        source_day=release.astimezone(local_zone).date()
        loft=(float(row["loft_lat"]),float(row["loft_lon"]))
        fixes=sorted(x for x in tracks[bird] if x[0]>=release)
        arrival=None
        for stamp,lat,lon in fixes:
            if stamp.astimezone(local_zone).date()!=source_day:continue
            if meters(*loft,lat,lon)<=loft_radius_m:
                arrival=stamp;break
        censored=arrival is None and row["same_day_tracking_complete"]!="true"
        seconds=(arrival-release).total_seconds() if arrival else None
        joined.append({
          "original_bird_id":bird,"original_session":row["session_id"],
          "treatment":row["treatment"],"gps_fixes":len(fixes),
          "arrival_utc":arrival.isoformat() if arrival else None,
          "seconds_after_release":seconds,
          "homed_within_70min":None if censored else arrival is not None and seconds<=4200,
          "homed_same_local_day":None if censored else arrival is not None,
          "right_censored":censored})
    summary={}
    for group in ("control","macrophage_depleted"):
        entries=[r for r in joined if r["treatment"]==group]
        complete=[r for r in entries if not r["right_censored"]]
        summary[group]={
          "birds":len(entries),"complete":len(complete),
          "censored":len(entries)-len(complete),
          "arrived_under_70min":sum(z["homed_within_70min"] is True for z in complete),
          "arrived_same_local_day":sum(z["homed_same_local_day"] is True for z in complete)}
    return {
       "source_DOI":"10.1126/science.ady2486",
       "loft_radius_m":loft_radius_m,"local_timezone":tz,
       "groups":summary,"per_bird":joined,
       "published_result_reproduced":False,
       "genuine_pigeon_compass_mechanism_proved":False
    }

def main():
    p=argparse.ArgumentParser(description=__doc__)
    for key in ("gps","metadata"):
        p.add_argument("--"+key,type=Path,required=True)
        p.add_argument("--"+key+"-sha256",required=True)
    p.add_argument("--local-timezone",required=True)
    p.add_argument("--loft-radius-m",type=float,required=True)
    p.add_argument("--out",type=Path)
    a=p.parse_args()
    gps,gs=read_rows(a.gps,a.gps_sha256)
    meta,ms=read_rows(a.metadata,a.metadata_sha256)
    result=reconstruct(gps,meta,a.local_timezone,a.loft_radius_m)
    result.update({"original_gps_sha256":gs,"original_reference_sha256":ms})
    txt=json.dumps(result,indent=2)+"\n"
    if a.out:a.out.write_text(txt)
    print(txt)
if __name__=="__main__":main()
