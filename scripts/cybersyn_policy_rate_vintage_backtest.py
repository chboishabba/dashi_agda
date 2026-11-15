#!/usr/bin/env python3
"""As-of forecast-vintage scoring for RBA/FOMC policy decisions.

Never backtest a prediction against a future outcome. Existing forecasts remain
pending until a separately sourced decision with later publication timestamp is
ingested. Different rate concepts (cash target vs Fed target midpoint) cannot
be interchanged; no market scenario is labelled a model forecast.
"""
from __future__ import annotations
import argparse, json
from datetime import datetime
from pathlib import Path

class VintageError(ValueError):
    pass

def utc(value):
    from datetime import timezone
    try:
        d = datetime.fromisoformat(value.replace("Z","+00:00"))
    except (ValueError, AttributeError) as ex:
        raise VintageError("invalid timestamp") from ex
    if d.tzinfo is None or d.utcoffset().total_seconds()!=0:
        raise VintageError("source dates must be explicit UTC")
    return d

def score(forecasts, decisions, *, as_of):
    now=utc(as_of)
    decisions_by_key={}
    for d in decisions:
        key=(d["bank"],d["decision_date"],d["target_metric"])
        published=utc(d["publication_utc"])
        if key in decisions_by_key:
            raise VintageError("duplicate decision")
        if not isinstance(d["rate_pct"],(int,float)):
            raise VintageError("invalid observed rate")
        if not d.get("official_source_url"):
            raise VintageError("missing official decision source")
        if published<=now:
            decisions_by_key[key]=d
    results=[]
    for f in forecasts:
        published=utc(f["as_of_utc"])
        event=utc(f["decision_date"]+"T23:59:59Z")
        if not published<=now or not published<event:
            raise VintageError("forecast revised after decision or future vintage")
        key=(f["bank"],f["decision_date"],f["target_metric"])
        if not f.get("source_url") or not isinstance(f["point_rate_pct"],(int,float)):
            raise VintageError("unattributed or missing point forecast")
        d=decisions_by_key.get(key)
        if d is None:
            results.append({"bank":f["bank"],"decision_date":f["decision_date"],
                            "status":"pending-official-decision",
                            "as_of_utc":f["as_of_utc"],"target_metric":f["target_metric"]})
            continue
        if utc(d["publication_utc"])<=published:
            raise VintageError("decision already published before forecast")
        err=f["point_rate_pct"]-d["rate_pct"]
        results.append({"bank":f["bank"],"decision_date":f["decision_date"],
                        "status":"scored","target_metric":f["target_metric"],
                        "predicted_pct":f["point_rate_pct"],"actual_pct":d["rate_pct"],
                        "error_bp":round(100*err,6),
                        "squared_error_bp2":round((100*err)**2,6),
                        "forecast_source":f["source_url"],"decision_source":d["official_source_url"]})
    return {"as_of_utc":as_of,"forecasts":results,
            "scored":sum(x["status"]=="scored" for x in results),
            "pending":sum(x["status"]!="scored" for x in results)}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--forecasts",type=Path,required=True)
    p.add_argument("--decisions",type=Path,required=True)
    p.add_argument("--as-of",required=True)
    a=p.parse_args()
    print(json.dumps(score(json.loads(a.forecasts.read_text()),
        json.loads(a.decisions.read_text()),as_of=a.as_of),indent=2,sort_keys=True))
if __name__=="__main__":
    main()
