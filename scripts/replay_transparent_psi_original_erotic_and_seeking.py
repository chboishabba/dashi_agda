#!/usr/bin/env python3
"""Original Transparent Psi (Kekecs et al. 2023) trial-data source replay.

Source of analysis contract (read before modifications):
 github.com/kekecsz/Transparent_psi_RR_materials/blob/master/
 TPP_Statistical_analysis_script_FINAL.R
Original 11 born-open CSV shards:
 github.com/kekecsz/transparent-psi-results/tree/master/live_data
Combined original OSF CSV: https://osf.io/24qkr/download

Run (when original source bytes are available):
 python scripts/replay_transparent_psi_original_erotic_and_seeking.py \
    --combined final_combined_live_data_for_analysis.csv --out summary.json
OR --directory path/to/original/live_data

No participant-level data/ID strings are written to output. ALL
sensation-seeking tests are EXPLORATORY, not the original preregistered
primary confirmatory mixed-effects logistic model. Use the original R
script for source-exact 4-test stopping, Bayesian robust and GLMM replay.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import re
import numpy as np
import pandas as pd
from scipy.stats import pearsonr
import statsmodels.api as sm

STOP=37836
EXPECTED_EROTIC_PARTICIPANTS=2115
RAW_COLUMNS=["timestamp","participant_ID","experimenter_ID_code",
 "experimenter_ASGS_total_score","laboratory_ID_code","sitePI_ASGS_total_score",
 "session_type","consent_screen_answer",
 "refused_to_answer_sexual_orientation_question","age","sex","final_consent",
 "ESP_Q_item_1","ESP_Q_item_2","ESP_Q_item_3","SS_Q_item_1","SS_Q_item_2",
 "trial_number","guessed_side","target_side","reward_type","sides_match"]
# Author R source (lines 214-216) lists these test-lab IDs.
LAB_IDS_TO_EXCLUDE=[
 "", "18155ef201564afbb81f6a8b74aa9a033eac51ec6595510eca9606938ffaced3",
 "ece83ceb8611d1926746e5bb3597ed1e8cb5d336521331b31961d5c0348883cf",
 "bd2dd15be34863e9efb77fbddfe744382a9c62c6a497e8bcf3097a47905b905b",
 "fff9cb9dcc3ac735fc25a59f424e98278a731c23ccd57276d292996c2ba7784f",
]
SEEKING_LABELS=["very untrue","untrue","between true and untrue",
                "true","very true"]
def read_original_csv(path:Path)->pd.DataFrame:
    # The original code explicitly handles the first CSV shards that were
    # written without a header. Preserve source row order (not sorting by
    # hashed timestamps).
    with path.open(encoding="utf-8-sig",newline="") as handle:
        first=handle.readline()
    named=first.startswith("timestamp")
    d=pd.read_csv(path,dtype=str,header=0 if named else None,
                  names=None if named else RAW_COLUMNS,keep_default_na=True)
    assert list(d.columns)==RAW_COLUMNS,(path,list(d.columns))
    return d

def date_in_filename(file:Path):
    match=re.search(r"_(\d{1,2})-(\d{1,2})-(\d{4})\.csv$",file.name)
    if not match: raise ValueError(f"Unexpected source basename: {file.name}")
    day,month,year=map(int,match.groups())
    return year,month,day

def load_original(directory:Path|None,combined:Path|None)->pd.DataFrame:
    if (directory is None)==(combined is None):
        raise ValueError("Supply exactly one of --directory or --combined")
    if combined is not None:
        return read_original_csv(combined)
    files=sorted(directory.glob("*.csv"),key=date_in_filename)
    if len(files)!=11:
        raise ValueError(f"Expected exactly 11 original dated CSV shards, got {len(files)}")
    return pd.concat([read_original_csv(p) for p in files],ignore_index=True)

def score_seeking(value:str,reverse:bool)->float:
    try: v=SEEKING_LABELS.index(str(value).strip().lower())+1
    except ValueError:return np.nan
    return float(6-v if reverse else v)

def replay(df:pd.DataFrame)->dict:
    # Author R source: filter test labs; retain all real erotic trials
    # (including unfinished participant sessions), stop first 37,836.
    data=df.loc[~df["laboratory_ID_code"].isin(LAB_IDS_TO_EXCLUDE)
                & df["laboratory_ID_code"].notna()].copy()
    valid_trials=data.loc[data["trial_number"].notna()]
    erotic=valid_trials.loc[valid_trials["reward_type"].str.lower()=="erotic"].copy()
    assert len(erotic)>=STOP, f"only {len(erotic)} valid erotic trials"
    primary=erotic.iloc[:STOP].copy()
    matched=primary["sides_match"].str.lower().map({"true":1,"false":0})
    assert matched.notna().all()
    primary["hit"]=matched.astype(int)
    n=primary["participant_ID"].nunique()
    y=int(primary["hit"].sum())
    assert len(primary)==STOP
    assert n==EXPECTED_EROTIC_PARTICIPANTS,(n,EXPECTED_EROTIC_PARTICIPANTS)
    # Published 49.89% rounding, actual integer y disclosed ONLY after
    # original CSV acquisition.
    assert 49885*STOP <= y*100000 < 49895*STOP,(y,STOP)
    parts=primary.groupby("participant_ID",sort=False).agg(
        successes=("hit","sum"),trials=("hit","size"),
        lab=("laboratory_ID_code","first"),
        seeking1=("SS_Q_item_1","first"),
        seeking2=("SS_Q_item_2","first"),
        esp_belief=("ESP_Q_item_1","first"))
    parts["rate"]=parts.successes/parts.trials
    # Source official descriptive method (R lines 416-421):
    # SS_Q_item_1 is REVERSE-coded, second item is NOT.
    parts["ss1"]=parts.seeking1.map(lambda v:score_seeking(v,True))
    parts["ss2"]=parts.seeking2.map(lambda v:score_seeking(v,False))
    parts["seeking"]=parts[["ss1","ss2"]].mean(axis=1)
    parts.loc[parts[["ss1","ss2"]].isna().any(axis=1),"seeking"]=np.nan
    known=parts.dropna(subset=["seeking"])
    # Bem's 2011 score is NOT the same validated scale; >2.5 is an
    # EXPLORATORY, cross-instrument sensitivity analysis, not a
    # preregistered direct replication of Bem's subgroup cutoff.
    high=known.seeking>2.5
    summary={
      "scope":"real source-raw replication; nonpreregistered moderator reanalysis",
      "main_erotic_trials":STOP,
      "main_participants":n,
      "observed_hits":y,
      "observed_hit_rate":y/STOP,
      "published_rounded_hit_rate":.4989,
      "participants_with_both_sensation_items":len(known),
      "sensation_seeking_scale":"(6-coded_item1 + coded_item2)/2; ordinal 1..5",
      "high_seeking_threshold_is_posthoc_cross_instrument":True,
      "exploratory_high_n":int(high.sum()),
      "exploratory_low_n":int((~high).sum()),
      "exploratory_high_mean_participant_rate":float(known.loc[high,"rate"].mean()),
      "exploratory_low_mean_participant_rate":float(known.loc[~high,"rate"].mean()),
      "exploratory_high_trial_pooled_rate":float(
         known.loc[high,"successes"].sum()/known.loc[high,"trials"].sum()),
      "exploratory_low_trial_pooled_rate":float(
         known.loc[~high,"successes"].sum()/known.loc[~high,"trials"].sum()),
      "warning":"For source-exact preregistered result, run author's lme4 GLMM and 3 Bayes factors. No original trial outputs committed.",
    }
    if len(known)>=20 and known.seeking.nunique()>1:
        p=pearsonr(known.seeking,known.rate)
        summary["exploratory_seeking_rate_r"]=float(p.statistic)
        summary["exploratory_seeking_rate_two_sided_p"]=float(p.pvalue)
        # Participant-level binomial aggregate GLM, robust HC3 errors;
        # sensitivity model, NOT authors' predeclared random-intercept GLMM.
        x=sm.add_constant(known["seeking"].astype(float))
        resp=known.successes/known.trials
        model=sm.GLM(resp,x,family=sm.families.Binomial(),
                     var_weights=known.trials).fit(cov_type="HC3")
        summary["exploratory_binomial_glm_robust_seeking_coef"]=float(model.params["seeking"])
        summary["exploratory_binomial_glm_robust_seeking_p"]=float(model.pvalues["seeking"])
        summary["exploratory_glm_method"]="participant-binomial aggregated HC3 (NOT original preregistered lme4)"
    return summary

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--combined",type=Path)
    p.add_argument("--directory",type=Path)
    p.add_argument("--out",type=Path)
    args=p.parse_args()
    result=replay(load_original(args.directory,args.combined))
    s=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if args.out: args.out.write_text(s,encoding="utf8")
    print(s)

if __name__=="__main__":main()
