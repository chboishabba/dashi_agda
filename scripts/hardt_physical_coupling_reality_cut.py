#!/usr/bin/env python3
"""Hardt 2026 source-aware biomagnetic detection/actuation model.
Defaults are SYNTHETIC; no human neural field, target, remote effect,
or harmful mechanism has been measured. Based on published magnetophosphene
and brain/spinal OPM sources, with independent author attribution.
"""
from __future__ import annotations
import argparse, hashlib, json, math, zipfile
from pathlib import Path

DATA_V2={"main":"https://zenodo.org/records/20824565",
         "other":"https://zenodo.org/records/20824827",
         "superseded_other_v1":"https://zenodo.org/records/19029856",
         "official_leadfields_md5":"0b6ceaa0db22ce9cb94ad46ee05deb5a",
         "source":"Spedden, Schmidt, O'Neill et al., Current Biology 2026",
         "physical_forward":"v2 Biot-Savart current dipole in three axes",
         "v1_forward":"superseded BEM lead field",
         "participant_count":9,"main_count":7,"other_count":2,
         "opm_sensors":64,"opm_axes_per_sensor":3,
         "opm_sampling_hz":1500,"emg_sampling_hz":1000,
         "anatomically_coregistered_subject":"OP00212",
         "network_frequency_hz":[10,35]}
EXPECTED=("geometries_experimental_withbrain.mat",
          "leadfield_experimental_bslaw_experimental.mat","T.mat")

def illustrative_physics():
    # Hypothetical MEG 100fT PEAK at 0.1m, N=100, 10m target,
    # 2Hz oscillation; point-dipole inverse-cube in the stated regime.
    near=100e-15; r0=.1; r=10.; n=100; f=2.; loop_radius=.1
    decay=(r0/r)**3
    far_aligned=near*decay*n
    far_unaligned=near*decay*math.sqrt(n)
    # Uniform axial sinusoidal B over ideal circular loop:
    # peak tangential E=pi*freq*radius*B_peak.
    Epeak=math.pi*f*loop_radius*far_aligned
    # Published 2026 magnetophosphene global exposure source example:
    # 20Hz, 31.5mT_RMS (50% probability). DIFFERENT physiology/geometry.
    published_global_B_rms=.0315; published_f=20.
    comparison_Erms=math.pi*published_f*loop_radius*published_global_B_rms
    hypothetical_Erms=Epeak/math.sqrt(2)
    ratio=comparison_Erms/hypothetical_Erms
    assert abs(decay-1e-6)<1e-18 and abs(far_aligned-1e-17)<1e-29
    assert 1e16 < ratio < 1e18
    return {"status":"ILLUSTRATIVE_ASSUMPTIONS_NOT_MEASUREMENTS",
            "near_peak_T_assumed":near,"reference_distance_m":r0,
            "receiver_distance_m":r,"ideal_coherent_people":n,
            "oscillation_hz":f,"loop_radius_m":loop_radius,
            "dipole_attenuation":decay,"far_coherent_B_peak_T":far_aligned,
            "far_uncorrelated_phase_amplitude_scale_T":far_unaligned,
            "uniform_loop_E_peak_V_per_m":Epeak,
            "different_global_20Hz_comparator_B_RMS_T":published_global_B_rms,
            "different_global_20Hz_E_RMS_ideal_V_per_m":comparison_Erms,
            "comparison_ratio_NOT_an_empirical_neural_threshold":ratio,
            "comparator_source_doi":"10.1038/s41598-026-44440-5",
            "limits":"Point dipole, 100fT assumed, ideal coherence, uniform loop; retinal 20Hz response cannot be read as delta brain response or universal no-go. Radical-pair receptors and new couplings need separate tests."}

def frequency_scope():
    assert 4 < 10 and not .5 <= 20 <= 4
    return {"delta_hz":[.5,4],"human_brain_spinal_EMG_network_hz":[10,35],
            "retinal_global_exposure_comparator_hz":20,
            "frequency_identity_refused":True}

def audit_original_leadfields(path:Path):
    """Fail closed unless original author-provided v2 ZIP content is acquired.
    Validation is a source-model object receipt, NOT neural data reproduction.
    """
    raw=path.read_bytes()
    md5=hashlib.md5(raw).hexdigest(); sha=hashlib.sha256(raw).hexdigest()
    if md5!=DATA_V2["official_leadfields_md5"]:
        return {"admitted":False,"reason":"wrong original v2 ZIP digest",
                "observed_md5":md5,"sha256":sha,"size_bytes":len(raw)}
    try:
        with zipfile.ZipFile(path) as z:
            files=z.namelist()
            missing=[item for item in EXPECTED if not any(
                f==item or f.endswith("/"+item) for f in files)]
            if missing:
                return {"admitted":False,"reason":"v2 Biot-Savart member missing",
                        "missing":missing,"sha256":sha}
            bad=z.testzip()
            if bad:
                return {"admitted":False,"reason":"archive CRC mismatch","member":bad}
    except (OSError,zipfile.BadZipFile) as exc:
        return {"admitted":False,"reason":"invalid ZIP","error":str(exc)}
    return {"admitted":True,"source_dataset_version":"v2",
            "source_claim":"original precomputed Biot-Savart forward geometry",
            "md5":md5,"sha256":sha,"expected_members":list(EXPECTED),
            "participant_data_replayed":False,"physical_effect_measured_here":False}

def main():
    p=argparse.ArgumentParser()
    p.add_argument("--v2-leadfields-zip",type=Path,default=None)
    args=p.parse_args()
    out={"source_metadata_NOT_dataset_bytes":DATA_V2,
         "physical_illustration":illustrative_physics(),
         "frequency_provenance":frequency_scope(),
         "v2_original_leadfields":"NOT_ACQUIRED"}
    if args.v2_leadfields_zip:
        out["v2_original_leadfields"]=audit_original_leadfields(args.v2_leadfields_zip)
    print(json.dumps(out,indent=2,sort_keys=True))
if __name__=="__main__":main()
