#!/usr/bin/env python3
"""J23 native-source 11-fold clock reduction and 2-event Poincare continuation.

Uses unmodified J18/J19/J20/J21/J22 source owners. Conditional synthetic wave
and nine-state switching circuit only; no original Filsinger pin/physical
source assertion. Finite corner continuation is not interval ODE validation.
Run locally, no CI: --mode fundamental; --mode corners --start 0 --count 8.
"""
import argparse
import itertools
import json
import math
import numpy as np
import sympy as S
import check_smith_filsinger_j18_hf_spark_tank_20261123 as hf
import check_smith_filsinger_j19_zero_freewheel_inverse_20261123 as j19
import check_smith_filsinger_j20_perfect_capture_reactive_return_20261123 as j20
import check_smith_filsinger_j21_source_only_throughput_20261123 as j21
import check_smith_filsinger_j22_saltation_shooting_20261123 as j22

SHA = {
    "J18": "f4270a475f010874056cfe3cdeff5ee8e43c44eb",
    "J19": "cc5cec2d4f881b38b4c01ef79dd93f36e9ef1439",
    "J20": "ed09b82287ec1ca0318b4f8e9d355f614d00d894",
    "J21": "b4c865f465f1a4a2e8dd40820eb02a6456454d67",
    "J22": "5b2b84b247630d10794fa2f91617a82ac4e318fc",
}
P0 = j22.P.copy()
ROOT = np.array([
    -.04585851023051101, .09671204057003767, 1.9865816276789396,
    1.189065091000899, 2.38393479550165, 5.502919318567719,
    -5.781120275382999, -.7451738522603922, -1.558522667501921,
])
EPS = dict(gamma_rad=.0001, gamma_internal=.00005, k=.0005,
           kh=.0005, Gload=.0005)
TAU = 2*math.pi/P0["omega"]
T = hf.native.T

def source_guard():
    for key, module in (("J18",hf),("J19",j19),("J20",j20),
                        ("J21",j21),("J22",j22)):
        assert j20.blob(module.__file__) == SHA[key], (key, "source drift")
    assert P0["drive_amp"] == 0
    assert P0["wave_handedness"] == -1
    assert P0["off_return"] == "capacitive"
    assert abs(T - 11*TAU)<1e-12
    assert P0["Rcoil"]>0 and P0["Gload"]>0
    t, phi=S.symbols("t phi",real=True)
    w=S.Rational(11,10)
    tau_exact=2*S.pi/w
    assert S.simplify(11*tau_exact-20*S.pi)==0
    assert S.simplify(S.sin(w*(t+tau_exact)+phi)-S.sin(w*t+phi))==0
    assert S.simplify(S.cos(w*(t+tau_exact)+phi)-S.cos(w*t+phi))==0
    # sin(t) driver does NOT have this shorter period: source-only scope.
    assert S.simplify(S.sin(tau_exact))!=0
    return dict(exact_tau="20*pi/11",source_cycles_per_J12_window=11,
                switching_mode_must_restore=True,driver_off_only=True)

def configure(p):
    j22.P.clear()
    j22.P.update(p)
    j22.T=TAU
    # L and A are UNCHANGED by the five varied coefficients;
    # j22.LI and j22.AI remain those of the original source.

def solve(p,seed=ROOT):
    configure(p)
    x=np.array(seed,copy=True)
    history=[]
    for _ in range(4):
        s=j22.switched_tangent(x,rtol=3e-10,atol=3e-12,max_step=.035)
        labels=[e["label"] for e in s["events"]]
        if labels!=["off","on"] or not s["end_on"]:
            return dict(accepted=False,reason="different events from current seed",
                        observed_labels=labels,iteration=len(history))
        d=float(max(abs(s["endpoint"]-x)))
        history.append(d)
        if d<5e-10:break
        x=x+np.linalg.solve(np.eye(9)-s["M"],s["endpoint"]-x)
    s=j22.switched_tangent(x,rtol=3e-10,atol=3e-12,max_step=.035)
    err=float(max(abs(s["endpoint"]-x)))
    slopes=[-s["events"][0]["signed_slope"],s["events"][1]["signed_slope"]]
    # In native J22 events, signed_slope is ALREADY direction corrected.
    slopes=[e["signed_slope"] for e in s["events"]]
    sv=np.linalg.svd(np.eye(9)-s["M"],compute_uv=False)
    y,on,w=hf.advance(j22.P,True,j22.PHASE,state=x,active=True,
                      t0=0.,T=TAU,rtol=3e-11,atol=3e-13,max_step=.025)
    ev=[label for _,label in w["event_log"]]
    res=dict(
       accepted=True,params={k:p[k] for k in EPS},
       newton_history=history,return_defect=err,
       event_labels=[e["label"] for e in s["events"]],
       event_times=[e["time"] for e in s["events"]],
       event_gap=s["events"][1]["time"]-s["events"][0]["time"],
       min_signed_crossing_slope=float(min(slopes)),
       spectral_radius=s["spectral_radius"],
       sigma_min_IminusM=float(min(sv)),
       numerical_root=x.tolist(),
       energy_residual=w["residual"],storage_delta=w["storage_delta"],
       independent_native_energy_replay_closure=float(max(abs(y-x))),
       input_energy=w["incident"],load_energy=w["hf_load"],
       output_energy=w["outgoing"],capture_ratio=w["net_wave"]/w["incident"],
       load_ratio=w["hf_load"]/w["incident"],
       driver_input=w["driver"])
    res["accepted"] = bool(
        res["event_labels"]==["off","on"] and ev==["off","on"] and on
        and min(slopes)>.04 and res["event_gap"]>.01
        and err<1e-8 and res["spectral_radius"]<.99
        and min(sv)>.08 and abs(w["residual"])<2e-7
        and abs(w["storage_delta"])<2e-7
        and res["independent_native_energy_replay_closure"]<1e-7
        and w["driver"]==0 and w["incident"]>0)
    if not res["accepted"]:
        res["reason"]="one or more native-source acceptance gates failed"
    return res

def fundamental():
    x=solve(P0)
    assert x["accepted"],x
    xroot=np.array(x["numerical_root"])
    configure(P0)
    short=j22.switched_tangent(xroot,rtol=1e-11,atol=1e-13,max_step=.025)
    j22.T=T
    long=j22.switched_tangent(xroot,rtol=1e-11,atol=1e-13,max_step=.025)
    j22.T=TAU
    assert len(short["events"])==2 and len(long["events"])==22
    rel=float(np.linalg.norm(long["M"]-np.linalg.matrix_power(short["M"],11))
              /np.linalg.norm(long["M"]))
    rho_short=short["spectral_radius"]
    rho_long=long["spectral_radius"]
    assert rel<1e-6 and abs(rho_short**11-rho_long)<1e-6
    ya,ona,wa=hf.advance(P0,True,j22.PHASE,state=xroot,active=True,t0=0.,
                        T=T,rtol=3e-11,atol=3e-13,max_step=.025)
    assert ona and len(wa["event_log"])==22
    assert abs(wa["hf_load"]-11*x["load_energy"])<2e-5
    assert abs(wa["incident"]-11*x["input_energy"])<2e-5
    return dict(status="J23_NATIVE_FUNDAMENTAL_CONSUMER_PASS_IF_EXECUTED",
      source_guard=source_guard(), source_blobs=SHA,
      fundamental=x, fundamental_monodromy_radius=rho_short,
      full_monodromy_radius=rho_long,monodromy_power_relative_error=rel,
      original_full_window_22_events=22, original_full_window_work=hf.simple(wa),
      full_window_state_closure=float(max(abs(ya-xroot))),
      exact_global_fixed_point_interval_certificate=False,
      physical_environmental_source_or_terminal_verified=False,
      github_actions_or_ci_run=False,agda_kernel_run=False)

def corners(start,count):
    source_guard()
    seq=list(itertools.product((-1,1),repeat=len(EPS)))
    rows=[]
    for i in range(start,min(32,start+count)):
        signs=seq[i]
        step={k:EPS[k]*s for k,s in zip(EPS,signs)}
        target=P0|{k:P0[k]+d for k,d in step.items()}
        r=solve(target)
        method="direct"
        if not r["accepted"]:
            method="warm-quarter-steps"
            previous=ROOT.copy()
            for fraction in (.25,.5,.75,1.):
                pp=P0|{k:P0[k]+fraction*d for k,d in step.items()}
                r=solve(pp,previous)
                if not r["accepted"]:break
                previous=np.array(r["numerical_root"])
        rows.append(dict(index=i,accepted=r["accepted"],
                         method=method,parameters={k:target[k] for k in EPS},
                         result={k:r.get(k) for k in ("load_ratio","capture_ratio",
                         "min_signed_crossing_slope","event_gap",
                         "spectral_radius","sigma_min_IminusM",
                         "return_defect","energy_residual","storage_delta",
                         "independent_native_energy_replay_closure")}))
        assert r["accepted"],(i,r)
    return dict(status="J23_NATIVE_FINITE_CORNERS_PASS_IF_EXECUTED",
      corners_checked=[start,min(32,start+count)],rows=rows,
      not_an_interval_enclosure_of_continuous_parameter_box=True,
      exact_global_fixed_point_interval_certificate=False,
      github_actions_or_ci_run=False,agda_kernel_run=False)

if __name__=="__main__":
    parser=argparse.ArgumentParser()
    parser.add_argument("--mode",choices=("fundamental","corners"),required=True)
    parser.add_argument("--start",type=int,default=0)
    parser.add_argument("--count",type=int,default=8)
    args=parser.parse_args()
    result=fundamental() if args.mode=="fundamental" else corners(args.start,args.count)
    print(json.dumps(result,indent=2,sort_keys=True))
