#!/usr/bin/env python3
"""Prepare verified Digital-ESD full texts for the generic SLR source-unit parser.

This is a thin adapter only. It does not parse, screen, promote claims, or create
SourceAuditAdmission.

Input: JSONL rows compatible with Digital-ESD verified full-text indexes.
Retained lane accepts include/probable. Resolution lane accepts reviewed
unresolved only when explicitly marked purpose=screening-resolution.
"""

from __future__ import annotations
import argparse, json
from pathlib import Path

RETAINED={"include","probable"}

def read_jsonl(path:Path):
    out=[]
    with path.open(encoding="utf-8") as f:
        for n,line in enumerate(f,1):
            if not line.strip(): continue
            row=json.loads(line)
            if not isinstance(row,dict): raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out

def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--fulltext-index",required=True,type=Path)
    ap.add_argument("--output",required=True,type=Path)
    ap.add_argument("--purpose",choices=["retained-study","screening-resolution"],default="retained-study")
    args=ap.parse_args()

    rows=read_jsonl(args.fulltext_index)
    out=[]
    seen=set()
    for row in rows:
        src=str(row.get("source_identity_reference") or "").strip()
        if not src or src in seen: raise ValueError(f"invalid/duplicate source identity: {src!r}")
        seen.add(src)
        if row.get("full_text_obtained") is not True:
            continue

        decision=str(row.get("screening_decision") or row.get("decision") or "")
        if args.purpose=="retained-study":
            if decision not in RETAINED:
                raise ValueError(f"{src}: retained-study parse requires include/probable, found {decision!r}")
            role="screened-digital-esd-study"
        else:
            if decision!="unresolved":
                raise ValueError(f"{src}: screening-resolution parse requires unresolved")
            if row.get("purpose_is_screening_resolution") not in (True,"true","True","1",1):
                raise ValueError(f"{src}: missing screening-resolution purpose receipt")
            role="digital-esd-screening-resolution"

        text_path=str(row.get("text_path") or "").strip()
        digest=str(row.get("full_text_sha256") or "").strip()
        identity=str(row.get("same_object_identity_review_reference") or "").strip()
        if not text_path or not digest or not identity:
            raise ValueError(f"{src}: incomplete full-text identity receipt")

        p=Path(text_path)
        if not p.is_file():
            raise ValueError(f"{src}: text artifact absent: {p}")

        out.append({
            "source_unit_ref":f"digital-esd:{src}:{digest}",
            "source_kind":"scholarly-full-text",
            "source_role":role,
            "language":str(row.get("language") or "en"),
            "revision_ref":f"fulltext-sha256:{digest}",
            "text_path":str(p),
            "digital_esd_source_identity_reference":src,
            "same_object_identity_review_reference":identity,
            "screening_decision":decision,
            "screening_decision_reference":row.get("screening_decision_reference"),
            "adapter_is_semantic_authority":False,
        })

    args.output.parent.mkdir(parents=True,exist_ok=True)
    with args.output.open("w",encoding="utf-8") as f:
        for row in out:
            f.write(json.dumps(row,ensure_ascii=False,sort_keys=True)+"\n")
    print(f"DIGITAL_ESD_SLR_SOURCE_UNITS purpose={args.purpose} source_units={len(out)} output={args.output}")
    return 0

if __name__=="__main__":
    raise SystemExit(main())
