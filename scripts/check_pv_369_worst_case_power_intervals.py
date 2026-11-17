#!/usr/bin/env python3
"""Conservative source-conditional P7 4T robust acceptance, NOT certification.

Consumes the result of check_pv_g173_same_sample_optics_eqe_iv_weld.py,
which already checked photon conservation, source optical Jsc, individual IV
and source input digests. Uniform *absolute bounded* relative errors on
the full IV curve (not one-sigma Gaussian standard errors) give
P_i,true in [P_i,nom*(1-uV)*(1-uJ), P_i,nom*(1+uV)*(1+uJ)].
Because this treats the envelope at every V, conservative MPP upper/lower
bounds hold only if the stated errors bound *all voltages and currents and
unseen IV maxima* over the complete V-range. The measured nominal JV MPP
must not have escaped the IV sweep.

The model requires explicit uncertainty bounds for incident spectrum, JV
voltage, JV current, electrical conversion and ALL auxiliary/driver ports.
No default 0 for physical uncertainties. A positive flag is CONDITIONAL
on externally authenticated systematic bounds and same-source controls.
IEC 60904-1:2020 and IEC 60904-9:2020 motivate, but do NOT certify, them.
"""
import argparse, json
from pathlib import Path
import math

def number(x,name,lower=0,upper=None):
    if isinstance(x,bool) or not isinstance(x,(int,float)) or not math.isfinite(x):
        raise ValueError(name+" not finite numeric")
    if x<lower or upper is not None and x>upper:
        raise ValueError(name+" outside admitted source interval")
    return float(x)

def bound_receipt(data,unc):
    if data.get("real_world_certified") is not False:
        raise ValueError("must retain explicit no-certification status")
    source=data.get("declared_provenance")
    if not isinstance(source,dict) or not source.get("sample_id") or not source.get("source_document") or not source.get("input_sha256") or not source.get("incident_spectrum_sha256"):
        raise ValueError("missing same-sample raw-data hashes and provenance")
    solar=number(data["incident_solar_W_m2"],"incident",1e-12)
    per=data.get("four_terminal_per_junction")
    if not isinstance(per,list) or len(per)<2 or len(per)>5:
        raise ValueError("missing actual independently contacted IV curves")
    for key in ("solar_rel_bound","voltage_rel_bound","current_rel_bound",
                "converter_efficiency_abs_bound","auxiliary_abs_bound_W_m2",
                "drive_abs_bound_W_m2","recovered_abs_bound_W_m2"):
        if key not in unc:raise ValueError("explicit uncertainty missing: "+key)
    solarErr=number(unc["solar_rel_bound"],"solar",0,.99)
    vErr=number(unc["voltage_rel_bound"],"voltage",0,.99)
    iErr=number(unc["current_rel_bound"],"current",0,.99)
    etaErr=number(unc["converter_efficiency_abs_bound"],"eta",0,1)
    auxErr=number(unc["auxiliary_abs_bound_W_m2"],"aux",0)
    driveErr=number(unc["drive_abs_bound_W_m2"],"drive",0)
    recoveryErr=number(unc["recovered_abs_bound_W_m2"],"recovered",0)
    if not all(key in unc for key in ("auxiliary_nominal_W_m2","drive_nominal_W_m2",
                                    "recovered_nominal_W_m2")):
        raise ValueError("all signed nominal auxiliary ports must be measured")
    aux=number(unc["auxiliary_nominal_W_m2"],"auxnom",0)
    drive=number(unc["drive_nominal_W_m2"],"drivenom",0)
    recovered=number(unc["recovered_nominal_W_m2"],"recnom",0)
    if recovered>drive:raise ValueError("recovered drive greater than input drive")
    lower=0.;upper=0.;gross=0.
    for p in per:
        v=number(p["gross_mpp_W_m2"],"gross",0)
        eta=number(p["converter_eta"],"converter",0,1)
        delivered=number(p["delivered_mpp_W_m2"],"delivered",0)
        if abs(delivered-v*eta)>1e-8*max(1,delivered,v):
            raise ValueError("source gross MPP and converter-delivered power disagree")
        gross+=v*eta
        lower+=v*(1-vErr)*(1-iErr)*max(0,eta-etaErr)
        upper+=v*(1+vErr)*(1+iErr)*min(1,eta+etaErr)
    nominalNet=gross-aux-drive+recovered
    sourceNet=number(data["four_terminal_net_W_m2"],"source nominal net",-1e12)
    if abs(nominalNet-sourceNet)>1e-8*max(1,abs(sourceNet),abs(nominalNet)):
        raise ValueError("uncertainty costs changed the original P5 signed electrical ledger")
    lowerNet=lower-(aux+auxErr)-(drive+driveErr)+max(0,recovered-recoveryErr)
    upperNet=upper-max(0,aux-auxErr)-max(0,drive-driveErr)+(recovered+recoveryErr)
    if lowerNet>nominalNet+1e-8 or upperNet<nominalNet-1e-8:
        raise ValueError("error interval does not enclose nominal")
    return {
      "declared_sample_id":source["sample_id"],
      "declared_source":source["source_document"],
      "input_sha256":source["input_sha256"],
      "incident_spectrum_sha256":source["incident_spectrum_sha256"],
      "temperature_K":source.get("temperature_K"),
      "solar_lower_W_m2":solar*(1-solarErr),
      "solar_upper_W_m2":solar*(1+solarErr),
      "net_lower_W_m2":lowerNet,"net_upper_W_m2":upperNet,
      "nominal_net_W_m2":nominalNet,
      "nominal_eta_pct":100*nominalNet/solar,
      "worst_case_net_eta_pct":100*lowerNet/(solar*(1+solarErr)),
      "best_case_net_eta_pct":100*upperNet/(solar*(1-solarErr)),
      "strict_robust_above_half":2*lowerNet>solar*(1+solarErr),
      "over_half_possible":2*upperNet>solar*(1-solarErr),
      "calibration_authenticity_confirmed":False,
      "IEC_60904_conformant_proven":False,
      "uncertainty_kind":"externally declared simultaneous deterministic absolute bounds, NOT statistical confidence",
      "original_2T_assembly_certified":False
    }

def compare(candidate,control):
    if candidate["declared_sample_id"]==control["declared_sample_id"]:
        raise ValueError("a distinct physical no-369 control sample must be identified")
    if candidate["declared_source"]!=control["declared_source"]:
        raise ValueError("matched source provenance mismatch")
    if candidate["incident_spectrum_sha256"]!=control["incident_spectrum_sha256"]:
        raise ValueError("actual calibrated incident spectrum digest differs across controls")
    if candidate["solar_lower_W_m2"]>control["solar_upper_W_m2"] or control["solar_lower_W_m2"]>candidate["solar_upper_W_m2"]:
        raise ValueError("disjoint same-source solar conditions")
    return {"strict_369_gain_worst_case":candidate["net_lower_W_m2"]>control["net_upper_W_m2"],
            "lower_gain_W_m2":candidate["net_lower_W_m2"]-control["net_upper_W_m2"],
            "upper_gain_W_m2":candidate["net_upper_W_m2"]-control["net_lower_W_m2"],
            "joint_model_gate":candidate["strict_robust_above_half"] and candidate["net_lower_W_m2"]>control["net_upper_W_m2"],
            "actually_certified_or_369_attributed":False}

def selftest():
    checks=[]
    def ck(name,ok):
        assert bool(ok),name
        checks.append(name)
    def receipt(net=510.,sample="369",solar=1000):
        return {"real_world_certified":False,
            "declared_provenance":{"sample_id":sample,"source_document":"same-simulator-session",
              "temperature_K":298.15,"incident_spectrum_sha256":"hash",
              "input_sha256":{"spectrum":"hash"}},
            "incident_solar_W_m2":solar,
            "four_terminal_net_W_m2":net,
            "four_terminal_per_junction":[{"gross_mpp_W_m2":net/4,"converter_eta":1.,"delivered_mpp_W_m2":net/4} for _ in range(4)]}
    def err(rel=0.,aux=0., solar=.0):
        return {"solar_rel_bound":solar,"voltage_rel_bound":rel,
          "current_rel_bound":rel,"converter_efficiency_abs_bound":0.,
          "auxiliary_nominal_W_m2":aux,"auxiliary_abs_bound_W_m2":0.,
          "drive_nominal_W_m2":0.,"drive_abs_bound_W_m2":0.,
          "recovered_nominal_W_m2":0.,"recovered_abs_bound_W_m2":0.}
    a=bound_receipt(receipt(),err())
    ck("strict 510 W > 500 W",a["strict_robust_above_half"])
    ck("nominal 51 pct",abs(a["nominal_eta_pct"]-51)<1e-12)
    ck("exact 500 W fails",not bound_receipt(receipt(500),err())["strict_robust_above_half"])
    ck("499 W fails",not bound_receipt(receipt(499),err())["strict_robust_above_half"])
    ck("5 pct uniform V and I uncertainty fails",not bound_receipt(receipt(),err(.05))["strict_robust_above_half"])
    ck("1 pct uniform V and I uncertainty fails",not bound_receipt(receipt(),err(.01))["strict_robust_above_half"])
    ck("0.5 pct V,J error passes",bound_receipt(receipt(),err(.005))["strict_robust_above_half"])
    ck("1 pct solar upper passes zero IV uncertainty",bound_receipt(receipt(),err(solar=.01))["strict_robust_above_half"])
    ck("2 pct solar upper fails",not bound_receipt(receipt(),err(solar=.02))["strict_robust_above_half"])
    ck("aux cost can erase gain",not bound_receipt(
        {**receipt(),"four_terminal_net_W_m2":499.},err(aux=11))["strict_robust_above_half"])
    ck("nominal interval enclosure",a["net_lower_W_m2"]<=a["nominal_net_W_m2"]<=a["net_upper_W_m2"])
    base=bound_receipt(receipt(504,"conventional"),err())
    ck("positive robust 369 gain",compare(a,base)["joint_model_gate"])
    loose=bound_receipt(receipt(),err(.015))
    ck("uncertain overlapping intervals fail 369",not compare(loose,base)["strict_369_gain_worst_case"])
    ck("overlapping intervals fail joint",not compare(loose,base)["joint_model_gate"])
    def rejected(fn):
        try:fn()
        except (ValueError,KeyError):return True
        return False
    ck("missing source hashes fail",rejected(lambda:bound_receipt({**receipt(),"declared_provenance":{}},err())))
    ck("cannot erase original declared auxiliary cost",rejected(lambda:bound_receipt(receipt(),err(aux=2))))
    ck("cannot forge more gross converter delivery",rejected(lambda:bound_receipt(
        {**receipt(),"four_terminal_per_junction":[{"gross_mpp_W_m2":127.5,
           "converter_eta":1.,"delivered_mpp_W_m2":150.} for _ in range(4)]},err())))
    ck("same sample cannot be control",rejected(lambda:compare(a,a)))
    ck("different solar provenance cannot be matched",rejected(lambda:compare(a,{**base,"declared_source":"different"})))
    ck("different spectrum bytes cannot be matched",rejected(lambda:compare(a,{**base,"incident_spectrum_sha256":"another"})))
    ck("missing relative bound fails",rejected(lambda:bound_receipt(receipt(),{k:v for k,v in err().items() if k!="solar_rel_bound"})))
    ck("invalid negative interval fails",rejected(lambda:bound_receipt(receipt(),{**err(),"current_rel_bound":-.1})))
    ck("invalid relative error >100% fails",rejected(lambda:bound_receipt(receipt(),{**err(),"current_rel_bound":1.2})))
    ck("fake certification not accepted",rejected(lambda:bound_receipt({**receipt(),"real_world_certified":True},err())))
    ck("even passing synthetic gate never certified",compare(a,base)["actually_certified_or_369_attributed"] is False)
    return {"checks_passed":len(checks),"all_passed":True,
      "synthetic_positive_case":a,"synthetic_control":base,
      "synthetic_matched_comparison":compare(a,base),
      "tests":checks}
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--selftest",action="store_true")
    p.add_argument("--candidate",type=Path)
    p.add_argument("--candidate-uncertainty",type=Path)
    p.add_argument("--control",type=Path)
    p.add_argument("--control-uncertainty",type=Path)
    p.add_argument("--output",type=Path)
    x=p.parse_args()
    if x.selftest:r=selftest()
    else:
        if not x.candidate or not x.candidate_uncertainty:
            p.error("candidate receipt and externally sourced bound JSON required")
        r={"candidate":bound_receipt(json.loads(x.candidate.read_text()),json.loads(x.candidate_uncertainty.read_text()))}
        if x.control or x.control_uncertainty:
            if not x.control or not x.control_uncertainty:
                p.error("control requires BOTH original receipt and bound JSON")
            r["control"]=bound_receipt(json.loads(x.control.read_text()),json.loads(x.control_uncertainty.read_text()))
            r["comparison"]=compare(r["candidate"],r["control"])
        r["independent_certification_claim"]=False
    if x.output:x.output.write_text(json.dumps(r,indent=2)+"\n")
    print(json.dumps(r,indent=2))
if __name__=="__main__":main()
