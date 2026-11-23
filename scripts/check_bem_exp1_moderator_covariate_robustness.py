#!/usr/bin/env python3
"""Exploratory source-accurate Bem EXP1 robustness, no participant-row export.

Uses original Bem session XLSX via artifact_tool (NOT 2023 raw trials).
Participant is the unit of analysis. Includes HC3 heteroscedastic-robust
regression and phase/sex-blocked permutation to guard against mere
source-analysis selection. The ORIGINAL 2011 one-sided Pearson correlation
r=.182, p=.03485 is primary-paper reporting, NOT a new preregistration.
A 20,000 permutation Monte Carlo has finite MC error; never call it proof
of precognition or a source-independent subgroup replication.
"""
from pathlib import Path
import argparse
import numpy as np
from scipy import stats
from artifact_tool import Blob,SpreadsheetFile
import statsmodels.formula.api as smf
import pandas as pd
import json
def replay(path:Path,seed=27717,repetitions=20000):
    wb=SpreadsheetFile.import_xlsx(Blob.load(str(path)))
    rows=wb.worksheets.get_item_at(0).get_range("A1:J101").values
    assert rows[0][7:10]==["Erotic.Hits.PC","Control.Hits.PC","Stimulus.Seeking"]
    assert len(rows)==101
    r=rows[1:]
    d=pd.DataFrame({
      "hit_pct":[x[7] for x in r],
      "control":[x[8] for x in r],
      "seek":[x[9] for x in r],
      "phase":[int(i>=40) for i in range(100)],
      "female":[int(x[4]=="Female") for x in r]})
    outcomes={}
    for formula in ["hit_pct ~ seek",
                    "hit_pct ~ seek + phase + female",
                    "hit_pct ~ seek*phase + female",
                    "hit_pct ~ seek + phase + female + control"]:
        model=smf.ols(formula,data=d).fit(cov_type="HC3")
        outcomes[formula]={"seeking_slope_pp_per_unit":float(model.params["seek"]),
          "seeking_two_sided_robust_p":float(model.pvalues["seek"]),
          "seeking_robust_95_ci":model.conf_int().loc["seek"].to_list(),
          "R_squared":float(model.rsquared)}
        if "seek:phase" in model.params:
            outcomes[formula]["seeking_by_phase_two_sided_p"]=float(model.pvalues["seek:phase"])
    x=d.seek.to_numpy(float)
    y=d.hit_pct.to_numpy(float)
    phase=d.phase.to_numpy(int)
    sex=d.female.to_numpy(int)
    observed=float(np.corrcoef(x,y)[0,1])
    groupidx=[np.where((phase==p)&(sex==s))[0]
              for p in [0,1] for s in [0,1]]
    rng=np.random.default_rng(seed)
    ge=0
    for _ in range(repetitions):
        xp=x.copy()
        for ids in groupidx: xp[ids]=rng.permutation(x[ids])
        ge+=np.corrcoef(xp,y)[0,1]>=observed
    block_perm_p=(1+ge)/(1+repetitions)
    phase_results=[]
    for p in [0,1]:
        subset=d[d.phase==p]
        high=subset[subset.seek>2.5]
        low=subset[subset.seek<=2.5]
        phase_results.append({"phase":p,"n_high":len(high),
          "n_low":len(low),"mean_high":float(high.hit_pct.mean()),
          "mean_low":float(low.hit_pct.mean())})
    assert abs(observed-0.182149095108172)<1e-9
    return {"original_r":observed,
      "source_2011_unadjusted_one_sided_p":float(stats.pearsonr(x,y).pvalue/2),
      "phase_sex_stratified_permutation_one_sided_p":float(block_perm_p),
      "permutations":repetitions,"seed":seed,
      "robust_models":outcomes,"phase_subgroups":phase_results,
      "warning":"Exploratory; original source effect reproduced, but reanalyses are not held-out. HC3 p values two-sided; original source prediction one-sided. No multiplicity or posthoc provenance inferred."}
if __name__=="__main__":
    p=argparse.ArgumentParser()
    p.add_argument("xlsx",type=Path)
    p.add_argument("--out",type=Path)
    p.add_argument("--permutations",type=int,default=20000)
    args=p.parse_args()
    result=replay(args.xlsx,repetitions=args.permutations)
    s=json.dumps(result,indent=2)+"\n"
    if args.out:args.out.write_text(s,encoding="utf-8")
    print(s)
