#!/usr/bin/env python3
"""EPBC 2019/8575: source-exact 42-row GHFF + bird OAG audit.

The original January-2026 Preliminary Documentation v5 Part A.i Tables
A63-65, A70-72, A77-79 provide all source rows. Authors are original
BAAM (Esk), One Environment (Avonvale), Saunders Havill (MWW). The
model uses the 2012 OAG's source-reproducing inverse-compound
(1 + annual_probability)^(-20) discount. This program does NOT silently
correct mutually inconsistent literal printed source values.

Cited original AU output numbers are source-authored claims, not observed
wildlife, and cannot be promoted to independent ecological equivalence,
agency findings, Court judgments, compliance breaches or payments.
"""
from __future__ import annotations
import argparse,json
from fractions import Fraction as F
from pathlib import Path

SITES=("Esk","Avonvale","Mount Walker West")
YEARS=20
P_VULNERABLE=F(2,1000)
P_CRITICALLY_ENDANGERED=F(68,1000)
IMPACT_AREA_Q=F("89.6")
IMPACT_FEATURES={"swift_parrot":9983,"regent_honeyeater":9868}
TARGET_A59={
  "flying_fox":{"Esk":"63.44","Avonvale":"60.59","Mount Walker West":"66.89"},
  "swift_parrot":{"Esk":"54.58","Avonvale":"53.49","Mount Walker West":"91.92"},
  "regent_honeyeater":{"Esk":"54.95","Avonvale":"12.07","Mount Walker West":"37.40"},
}
# Site rows: area ha, future-without OAG quality, future-with quality,
# confidence percent, source printed contribution percent.
GHFF={
  "Esk":[("150.1",5,8,75,"36.22"),("44.8",4,8,75,"10.81"),
         ("75.9",6,8,85,"13.84"),("9.4",5,8,85,"2.57")],
  "Avonvale":[("49.3",3,7,75,"15.86"),("15.2",3,7,75,"6.11"),
              ("2",4,6,85,"0.36"),("86.8",3,8,75,"34.91"),
              ("11",5,8,85,"3.01"),("3.7",6,7,85,"0.34")],
  "Mount Walker West":[("50.8",2,7,75,"20.43"),
           ("104.7",3,7,75,"33.68"),("62",5,7,85,"11.30"),
           ("8.1",5,7,85,"1.48")],
}
# Features: future-without offset, future with offset, confidence percent,
# published compensated percent. The two MWW swift rows below use the
# LITERAL Table A78/A16 Table17 "future without" column 30 and 109,
# even though published totals match start-values 207 and 20 instead.
FEATURES={
 "swift_parrot":{
   "Esk":[(8899,23407,75,"29.24"),(523,11255,75,"21.63"),
           (9108,10930,75,"3.67"),(423,442,75,"0.04")],
   "Avonvale":[(0,9860,75,"19.87"),(0,6080,75,"12.25"),
               (30,34,75,"0.01"),(109,10441,75,"20.82"),
               (0,264,75,"0.53"),(0,7,75,"0.01")],
   "Mount Walker West":[(0,16256,75,"32.76"),(0,26752,75,"53.92"),
                        (30,2708,75,"5.04"),(109,117,75,"0.20")]},
 "regent_honeyeater":{
   "Esk":[(214,14615,75,"29.36"),(149,10882,75,"21.88"),
           (8918,10740,75,"3.71"),(94,94,75,"0")],
   "Avonvale":[(0,5916,75,"12.06"),(0,0,75,"0"),(0,0,75,"0"),
               (0,0,75,"0"),(0,0,75,"0"),(0,4,75,"0.01")],
   "Mount Walker West":[(0,0,75,"0"),(0,16720,75,"34.09"),
                        (103,1667,75,"3.19"),(0,60,75,"0.12")]},
}

def discount(p):return (F(1)+p)**(-YEARS)
def percent_quality(area,before,after,confidence):
    return F(100)*F(area)*F(after-before,10)*F(confidence,100)*discount(P_VULNERABLE)/IMPACT_AREA_Q
def percent_features(sp,before,after,confidence):
    return F(100*(after-before))*F(confidence,100)*discount(P_CRITICALLY_ENDANGERED)/F(IMPACT_FEATURES[sp])
def fmt(x):return f"{float(x):.6f}"

def main_audit():
    assert discount(P_VULNERABLE)==F(1000,1002)**20
    assert discount(P_CRITICALLY_ENDANGERED)==F(1000,1068)**20
    report={"case":"EPBC 2019/8575",
            "source":"Proponent PD v5 Part A.i A63-65 A70-72 A77-79",
            "stage":"source-reported; unresolved source-cell contradictions",
            "units":"percent of impact compensation",
            "discount":"(1+annual extinction probability)^(-20)",
            "published_totals":TARGET_A59,
            "literal_input_reconciliation":{},
            "source_hard_conflicts":[],
            "independently_verified_species_outcome":False,
            "final_approved_15Oct_OAMP_verified":False,
            "actual_official_OAG_spreadsheet_executed":False}
    assert sum(len(rows) for rows in GHFF.values())==14
    assert all(sum(map(len,sp.values()))==14 for sp in FEATURES.values())
    for species,data in (("flying_fox",GHFF),*FEATURES.items()):
        assert set(data)==set(SITES)
        report["literal_input_reconciliation"][species]={}
        for site,rows in data.items():
            values=[]
            for i,row in enumerate(rows,1):
                if species=="flying_fox":
                    a,b,t,c,pub=row
                    predicted=percent_quality(a,b,t,c)
                else:
                    b,t,c,pub=row
                    predicted=percent_features(species,b,t,c)
                difference=predicted-F(pub)
                values.append(predicted)
                if abs(difference)>F(11,1000):
                    report["source_hard_conflicts"].append({
                      "species":species,"site":site,"AU":i,
                      "published_percent":pub,
                      "literal_recomputed_percent":fmt(predicted),
                      "percent_point_difference":fmt(difference),
                      "question":"Check literal OAG input cell, table transcription and version"})
            report["literal_input_reconciliation"][species][site]={
                "literal_recomputed_total_percent":fmt(sum(values,F())),
                "published_total_percent":TARGET_A59[species][site],
                "AU_count":len(rows)}
    assert len(report["source_hard_conflicts"])==4,report["source_hard_conflicts"]
    hard={(v["species"],v["site"],v["AU"]) for v in report["source_hard_conflicts"]}
    assert hard=={
       ("flying_fox","Esk",2),
       ("flying_fox","Avonvale",2),
       ("swift_parrot","Mount Walker West",3),
       ("swift_parrot","Mount Walker West",4)
    }
    # Additional HARD row/column identities, separate from OAG differences:
    assert 0+16720+1667+60==18447!=45833  # MWW regent A16 Table19
    assert 16256+26752+2708+117==45833 # MWW swift A16 Table17
    assert 0+0+30+109==139!=227 # MWW swift literal future-without total
    assert 0+0+207+20==227 # MWW swift source start total
    assert F("150.01")+F("47.72")+F("75.9")+F("9.4")==F("283.03")!=F("280.03") # Esk A64/A65
    assert 5495!=5496 # Esk A59 vs BAAM 7.3
    report["source_hard_conflicts"] += [
       {"species":"regent_honeyeater","site":"Mount Walker West",
        "issue":"Table 19 printed future value total 45833 != sum 18447; 45833 equals Swift Parrot Table 17 total"},
       {"species":"swift_parrot","site":"Mount Walker West",
        "issue":"Table 17 literal future-without rows total 139, printed total 227 (= START column total)"},
       {"species":"swift_parrot/regent_honeyeater","site":"Esk",
        "issue":"Tables A64/A65 literal AU feature-area values sum 283.03 ha vs printed 280.03 ha"},
       {"species":"regent_honeyeater","site":"Esk",
        "issue":"Main PD A59 54.95% differs from BAAM 7.3 54.96%"}
    ]
    report["numeric_row_conflicts"]=len(hard)
    report["other_source_total_conflicts"]=4
    report["reported_bird_plant_survival_percent"]=80
    # Conditional planting-survival multiplier assumes ALL *gain*
    # comes from 80%-surviving new plantings and no OAG nonlinearity.
    # This is separate from exact approved OAG. No survival rate measured.
    source_regent=F("104.42")
    report["regent_honeyeater_conditional_plant_survival"]={
       "80_percent_assumed_total_percent":"104.42",
       "75_percent_if_all_gains_scale_linearly":fmt(source_regent*F(75,80)),
       "70_percent_if_all_gains_scale_linearly":fmt(source_regent*F(70,80)),
       "survival_break_even_100_percent":fmt(F(80)*100/source_regent),
       "survival_break_even_90_percent":fmt(F(80)*90/source_regent),
       "is_official_OAG_scenario":False
    }
    return report

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--agda-file",type=Path)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    if args.agda_file:
        a=args.agda_file.read_text()
        for marker in ("mwwRegentRowSum","mwwRegentPrintedTotalNotRowSum",
                       "eskBirdLiteralAreaNotPrintedTotal",
                       "avonGHFFAU2GainInputsDiffer","eskGHFFAU2GainInputsDiffer"):
            assert marker in a,marker
        assert all(s not in a for s in ("postulate ","{!!}","allow-unsolved-metas"))
    report=main_audit()
    report["agda_source_marker_checked"]=bool(args.agda_file)
    out=json.dumps(report,indent=2,sort_keys=True)+"\n"
    if args.out:args.out.write_text(out)
    print(out,end="")
if __name__=="__main__":main()
