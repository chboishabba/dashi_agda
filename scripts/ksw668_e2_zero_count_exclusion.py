#!/usr/bin/env python3
"""E2 controlled SAME-SPECIMEN 14C nuclear-detection statistical exclusion.

One-sided Poisson bound P(N <= n | mean=mu_upper)=alpha.
If known physical background mean >= b_min and lower verified efficiency
eta_min > 0, conditional produced-event bound is
  S_upper = max(0,mu_upper-b_min)/eta_min.
Without real original specimen/protocol/control/assay data, no exclusion
follows. The original experimental RAW payload must match pinned SHA256.
This is not an experiment or evidence for emotion-induced transmutation.
"""
import argparse,hashlib,json,math,re
from pathlib import Path

def poisson_cdf(n,mean):
    if n<0 or mean<0:raise ValueError("Invalid Poisson domain")
    term=math.exp(-mean);total=term
    for j in range(1,n+1):
        term*=mean/j;total+=term
    return total

def one_sided_upper_mean(n,alpha=.05):
    if type(n) is not int or not 0<=n<=200:
        raise ValueError("Only original count 0..200 supported")
    if not 0<alpha<1:raise ValueError("Invalid confidence alpha")
    lo=0.;hi=max(10.,n+10*math.sqrt(n+1))
    while poisson_cdf(n,hi)>alpha:hi*=2
    for _ in range(96):
        mid=(lo+hi)/2
        if poisson_cdf(n,mid)>alpha:lo=mid
        else:hi=mid
    return (lo+hi)/2

def source_bound(receipt):
    needed=("original_file_sha256","original_authors_and_provenance",
        "individual_specimen_id","experimental_protocol","matched_control_id",
        "registered_isotope_assay","observed_count","efficiency_lower",
        "background_count_lower","exposure_seconds",
        "conditioned_nuclear_detection")
    missing=[k for k in needed if k not in receipt]
    if missing:raise ValueError("Missing original evidence: "+", ".join(missing))
    if not re.fullmatch("[a-fA-F0-9]{64}",receipt["original_file_sha256"]):
        raise ValueError("Missing genuine original hash")
    for key in needed[1:6]:
        if not isinstance(receipt[key],str) or not receipt[key].strip():
            raise ValueError("Missing controlled specimen/protocol/source "+key)
    if receipt["conditioned_nuclear_detection"] is not True:
        raise ValueError("AMS isotope observation not calibrated to nuclear counts")
    n=receipt["observed_count"];eff=receipt["efficiency_lower"]
    b=receipt["background_count_lower"];t=receipt["exposure_seconds"]
    if type(n) is not int or not 0<=n<=200:
        raise ValueError("Invalid original observed integer count")
    if any(not isinstance(v,(int,float)) or not math.isfinite(v)
           for v in (eff,b,t)) or not(0<eff<=1 and b>=0 and t>0):
        raise ValueError("No valid lower efficiency, background and live time")
    upper=one_sided_upper_mean(n)
    s=max(0.,upper-b)/eff
    return {
      "status":"CONDITIONAL one-sided Poisson 95% upper bound",
      "original_source_sha256":receipt["original_file_sha256"],
      "specimen":receipt["individual_specimen_id"],
      "observed_counts":n,"Poisson_total_upper_mean":upper,
      "produced_additional_events_upper":s,
      "hypothesized_additional_nuclear_reactions_per_second_upper":s/t,
      "assumptions":"Independent calibrated nuclear counts, known lower background and efficiency, genuine original exposure/assay/control",
      "universal_emotion_causation_excluded":False,
      "same_body_physical_exclusion_established":False
    }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--original-measurement",type=Path,required=True)
    ap.add_argument("--original-payload",type=Path,required=True,
                    help="Original raw bytes; must match source receipt digest")
    ap.add_argument("--out",type=Path)
    a=ap.parse_args()
    evidence=json.loads(a.original_measurement.read_text())
    digest=hashlib.sha256(a.original_payload.read_bytes()).hexdigest()
    if digest.lower()!=evidence.get("original_file_sha256","").lower():
        raise ValueError("Original experimental raw payload SHA-256 mismatch")
    out=source_bound(evidence)
    out["verified_original_payload_sha256"]=digest
    s=json.dumps(out,indent=2)+"\n"
    if a.out:a.out.write_text(s)
    print(s)
if __name__=="__main__":main()
