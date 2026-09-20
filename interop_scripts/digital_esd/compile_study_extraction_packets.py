#!/usr/bin/env python3
"""Compile generic SLR PNF records into Digital-ESD study review packets.

Automatic output is candidate-only. It nominates provenance-bearing sentence
spans against the existing 19-coordinate extraction schema; it does not mark
coordinates paid and cannot create SourceAuditAdmission.

Screening-resolution full text is routed to a separate ambiguity packet and is
never promoted to the retained-study audit lane.
"""

from __future__ import annotations
import argparse, hashlib, json, re
from pathlib import Path
from typing import Any

COORDINATES=[
 "sourceIdentityCoordinate","sourceKindAndRoleCoordinate","publicationDateCoordinate",
 "populationEducationLevelCoordinate","jurisdictionInstitutionContextCoordinate",
 "digitalTechnologyOrPracticeCoordinate","pedagogyCurriculumCompetenceCoordinate",
 "sustainabilityDimensionCoordinate","studyOrReviewDesignCoordinate",
 "outcomeOrClaimCoordinate","timeHorizonCoordinate","lifecycleBoundaryCoordinate",
 "circularityRepairabilityCoordinate","participantAgencyAuthorityCoordinate",
 "interoperabilityGovernanceCoordinate","externalityIncidenceCoordinate",
 "sameObjectStatusCoordinate","contextTransferCoordinate","uncertaintyLimitationCoordinate",
]

CUES={
 "populationEducationLevelCoordinate":{"student","students","teacher","teachers","learner","learners","school","schools","university","universities","higher","secondary","primary","adult","participant","participants"},
 "jurisdictionInstitutionContextCoordinate":{"country","countries","national","regional","institution","institutional","university","school","district","jurisdiction","community","communities"},
 "digitalTechnologyOrPracticeCoordinate":{"digital","online","technology","technologies","platform","platforms","artificial","intelligence","ai","ict","computer","computing","virtual","blended","mobile"},
 "pedagogyCurriculumCompetenceCoordinate":{"pedagogy","pedagogical","curriculum","curricular","competence","competency","competencies","teaching","learning","instruction","assessment"},
 "sustainabilityDimensionCoordinate":{"sustainability","sustainable","environment","environmental","climate","esd","ecological","social","economic"},
 "studyOrReviewDesignCoordinate":{"study","survey","interview","experiment","experimental","randomized","randomised","qualitative","quantitative","mixed","review","systematic","longitudinal","case"},
 "outcomeOrClaimCoordinate":{"outcome","outcomes","effect","effects","impact","impacts","result","results","finding","findings","increase","decrease","improve","improved","associated","association"},
 "timeHorizonCoordinate":{"year","years","month","months","week","weeks","longitudinal","follow","followup","duration","time","term"},
 "lifecycleBoundaryCoordinate":{"lifecycle","life","cycle","embodied","manufacturing","manufacture","production","deployment","operation","disposal","infrastructure"},
 "circularityRepairabilityCoordinate":{"circular","circularity","repair","repairability","reuse","reused","recycling","recycle","upgrade","durability","ewaste","waste"},
 "participantAgencyAuthorityCoordinate":{"voice","agency","participatory","participation","codesign","co-design","authority","decision","consent","learner","student"},
 "interoperabilityGovernanceCoordinate":{"governance","interoperability","interoperable","standards","standard","open","portability","migration","procurement","vendor"},
 "externalityIncidenceCoordinate":{"burden","benefit","cost","costs","externality","externalities","inequality","equity","distribution","distributed","affected","impact"},
 "contextTransferCoordinate":{"context","transfer","transferability","generalise","generalize","generalisability","generalizability","setting","settings","boundary","boundaries"},
 "uncertaintyLimitationCoordinate":{"limitation","limitations","uncertain","uncertainty","confidence","bias","caution","cannot","may","might","sample","constraint","constraints"},
}

def read_jsonl(path:Path)->list[dict[str,Any]]:
    out=[]
    with path.open(encoding="utf-8") as f:
        for n,line in enumerate(f,1):
            if not line.strip(): continue
            row=json.loads(line)
            if not isinstance(row,dict): raise ValueError(f"{path}:{n}: expected object")
            out.append(row)
    return out

def sha256_json(value:Any)->str:
    raw=(json.dumps(value,ensure_ascii=False,sort_keys=True,separators=(",",":"))+"\n").encode()
    return hashlib.sha256(raw).hexdigest()

def sentence_terms(candidate:dict[str,Any])->set[str]:
    terms=set()
    for row in candidate.get("dependency_rows",[]):
        for key in ("text","lemma"):
            v=str(row.get(key) or "").casefold()
            terms.update(re.findall(r"[a-z0-9]+",v))
    return terms

def locator(candidate:dict[str,Any],hits:list[str])->dict[str,Any]:
    return {
      "claim_candidate_id":candidate.get("claim_candidate_id"),
      "document_ref":candidate.get("document_ref"),
      "sentence_index":candidate.get("sentence_index"),
      "source_span_start":candidate.get("source_span_start"),
      "source_span_end":candidate.get("source_span_end"),
      "sentence_text_sha256":candidate.get("sentence_text_sha256"),
      "trigger_terms":hits,
      "candidate_only":True,
      "claim_truth_promoted":False,
    }

def coordinate_candidates(record:dict[str,Any],source_unit:dict[str,Any])->list[dict[str,Any]]:
    candidates=record.get("pnf_candidates",[])
    out=[]
    for coord in COORDINATES:
        spans=[]
        if coord=="sourceIdentityCoordinate":
            spans=[{"structural_reference":source_unit["digital_esd_source_identity_reference"],"candidate_only":False}]
        elif coord=="sourceKindAndRoleCoordinate":
            spans=[{"structural_reference":source_unit["source_role"],"candidate_only":False}]
        elif coord=="sameObjectStatusCoordinate":
            spans=[{"structural_reference":source_unit["same_object_identity_review_reference"],"candidate_only":False}]
        elif coord=="publicationDateCoordinate":
            spans=[]
        else:
            cues=CUES.get(coord,set())
            for cand in candidates:
                terms=sentence_terms(cand)
                hits=sorted(terms & cues)
                if hits:
                    spans.append(locator(cand,hits))
        out.append({
          "coordinate":coord,
          "candidate_evidence_spans":spans,
          "candidate_span_count":len(spans),
          "coordinate_paid":False,
          "review_required":True,
          "automatic_absence_inference":False,
        })
    return out

def main()->int:
    ap=argparse.ArgumentParser()
    ap.add_argument("--source-units",required=True,type=Path)
    ap.add_argument("--parser-manifest",required=True,type=Path)
    ap.add_argument("--output-dir",required=True,type=Path)
    args=ap.parse_args()

    source_units=read_jsonl(args.source_units)
    by_unit={str(x["source_unit_ref"]):x for x in source_units}
    manifest=read_jsonl(args.parser_manifest)
    args.output_dir.mkdir(parents=True,exist_ok=True)

    study_packets=[]
    resolution_packets=[]
    missing=[]

    for m in manifest:
        unit_ref=str(m.get("source_unit_ref") or "")
        source=by_unit.get(unit_ref)
        if source is None:
            raise ValueError(f"parser manifest source unit absent from adapter input: {unit_ref}")
        record_path=Path(str(m.get("record_path") or ""))
        if not record_path.is_file():
            missing.append(str(record_path))
            continue
        record=json.loads(record_path.read_text(encoding="utf-8"))
        if record.get("candidate_only") is not True or record.get("semantic_promotion") is not False:
            raise ValueError(f"{unit_ref}: parser authority boundary missing")

        base={
          "source_identity_reference":source["digital_esd_source_identity_reference"],
          "source_unit_ref":unit_ref,
          "revision_ref":record["revision_ref"],
          "source_text_sha256":m["source_text_sha256"],
          "same_object_identity_review_reference":source["same_object_identity_review_reference"],
          "screening_decision":source["screening_decision"],
          "screening_decision_reference":source.get("screening_decision_reference"),
          "parser_record_reference":str(record_path),
          "parser_document_ref":record["parser_receipt"]["document_ref"],
          "parser_model":record["parser_receipt"]["parser_model"],
          "parser_spacy_version":record["parser_receipt"]["spacy_version"],
          "pnf_candidate_count":len(record.get("pnf_candidates",[])),
          "parser_output_creates_claim_truth":False,
          "parser_output_creates_source_audit_admission":False,
        }

        if source["source_role"]=="digital-esd-screening-resolution":
            packet={
              "schema":"digital-esd-screening-resolution-parse-packet-v1",
              **base,
              "purpose":"screening-resolution",
              "candidate_pnf_refs":[x.get("claim_candidate_id") for x in record.get("pnf_candidates",[])],
              "creates_inclusion":False,
              "creates_exclusion":False,
              "creates_source_audit_admission":False,
            }
            packet["packet_reference"]="screening-resolution-parse:"+sha256_json(packet)
            resolution_packets.append(packet)
            continue

        coords=coordinate_candidates(record,source)
        packet={
          "schema":"digital-esd-study-extraction-candidate-packet-v1",
          **base,
          "purpose":"retained-study-audit",
          "extraction_schema_coordinate_count":19,
          "extraction_coordinates":coords,
          "study_claim_ceiling_coordinate":{
            "coordinate":"studyClaimCeiling",
            "paid":False,
            "review_required":True,
            "parser_output_cannot_raise_claim_ceiling":True,
          },
          "overlays":{
            "predicate_normal_form":{
              "candidate_refs":[x.get("claim_candidate_id") for x in record.get("pnf_candidates",[])],
              "review_required":True,
            },
            "intersectional_absence":{
              "status":"pending-source-bounded-review",
              "absence_may_not_be_inferred_from_unreported_demographics":True,
            },
            "material_environmental":{
              "status":"pending-source-bounded-review",
              "generic_infrastructure_average_may_not_become_deployment_footprint":True,
            },
          },
          "source_audit_admission_created":False,
          "source_audit_review_required":True,
        }
        packet["packet_reference"]="study-extraction-candidate:"+sha256_json(packet)
        study_packets.append(packet)

    if missing:
        raise FileNotFoundError("parser record files missing: "+", ".join(missing[:10]))

    def write(name:str,rows:list[dict[str,Any]]):
        p=args.output_dir/name
        with p.open("w",encoding="utf-8") as f:
            for row in rows:
                f.write(json.dumps(row,ensure_ascii=False,sort_keys=True)+"\n")
        return p

    study_path=write("study-extraction-candidate-packets.jsonl",study_packets)
    resolution_path=write("screening-resolution-parse-packets.jsonl",resolution_packets)
    summary={
      "schema":"digital-esd-study-parse-interop-summary-v1",
      "source_units":len(source_units),
      "parsed_manifest_rows":len(manifest),
      "retained_study_packets":len(study_packets),
      "screening_resolution_packets":len(resolution_packets),
      "study_packet_reference":str(study_path),
      "resolution_packet_reference":str(resolution_path),
      "automatic_coordinate_payment":False,
      "parser_output_creates_source_truth":False,
      "parser_output_creates_source_audit_admission":False,
    }
    (args.output_dir/"study-parse-summary.json").write_text(json.dumps(summary,indent=2,sort_keys=True)+"\n",encoding="utf-8")
    print(json.dumps(summary,sort_keys=True))
    return 0

if __name__=="__main__":
    raise SystemExit(main())
