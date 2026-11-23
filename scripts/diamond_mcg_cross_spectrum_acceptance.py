#!/usr/bin/env python3
"""Cross-spectral array detection acceptance. Requires measured JSON or --self-test.
No claimed physical validation: inputs and provenance are supplied by the caller.
Schema: instrument_id,dataset_source,dataset_sha256,calibration_id,bins;
each bin: frequency_hz,bandwidth_hz,response_t (complex [re,im] list),
noise_covariance_t2_per_hz (complex [re,im] matrix).
"""
import argparse,json,math
import numpy as np

def compute(data):
    for key in ("instrument_id","dataset_source","dataset_sha256","calibration_id","bins"):
        if not data.get(key): raise ValueError("missing source/calibration: "+key)
    total=0.; result=[]
    for b in data["bins"]:
        f=float(b["frequency_hz"]); df=float(b["bandwidth_hz"])
        if not (math.isfinite(f) and f>=0 and math.isfinite(df) and df>0):
            raise ValueError("invalid frequency/bin width")
        s=np.array([complex(*v) for v in b["response_t"]])
        C=np.array([[complex(*v) for v in row] for row in b["noise_covariance_t2_per_hz"]])
        n=len(s)
        if n<1 or C.shape!=(n,n) or not np.isfinite(s).all() or not np.isfinite(C).all():
            raise ValueError("invalid/non-finite array data")
        if not np.allclose(C,C.conj().T,rtol=1e-12,atol=0):
            raise ValueError("covariance not Hermitian")
        scale=np.max(np.abs(C))
        if scale<=0:raise ValueError("zero covariance")
        cn=C/scale
        eig=np.linalg.eigvalsh(cn)
        if eig[0]<=1e-12 or eig[-1]/eig[0]>=1e12:
            raise ValueError("covariance not SPD or numerically resolved")
        info=float(np.vdot(s,np.linalg.solve(cn,s)).real/scale)
        if not math.isfinite(info) or info<0:raise ValueError("invalid information")
        contribution=4*df*info
        total+=contribution
        result.append({"frequency_hz":f,"channel_count":n,"information_contribution":contribution})
    return {"conditional_known_signal_snr_squared":total,"bins":result,
            "source_attribution_certified":False,"data_authenticated":False}

def selftest():
    a={"instrument_id":"SYNTHETIC","dataset_source":"synthetic","dataset_sha256":"NOT-REAL",
       "calibration_id":"SYNTHETIC","bins":[{"frequency_hz":1.2,"bandwidth_hz":0.2,
       "response_t":[[1e-12,0],[1e-12,0]],
       "noise_covariance_t2_per_hz":[[[4e-24,0],[0,0]],[[0,0],[4e-24,0]]]}]}
    assert abs(compute(a)["conditional_known_signal_snr_squared"]-.4)<1e-12
    b=json.loads(json.dumps(a))
    b["bins"][0]["noise_covariance_t2_per_hz"][0][1]=[2e-24,0]
    b["bins"][0]["noise_covariance_t2_per_hz"][1][0]=[2e-24,0]
    assert compute(b)["conditional_known_signal_snr_squared"]<.4
    b["bins"][0]["noise_covariance_t2_per_hz"][1][0]=[0,0]
    try:compute(b)
    except ValueError:pass
    else:raise AssertionError("non-Hermitian input accepted")
    b=json.loads(json.dumps(a))
    b["bins"][0]["noise_covariance_t2_per_hz"][0][1]=[5e-24,0]
    b["bins"][0]["noise_covariance_t2_per_hz"][1][0]=[5e-24,0]
    try:compute(b)
    except ValueError:pass
    else:raise AssertionError("indefinite input accepted")
    print("PASS synthetic spectral controls, correlation and SPD rejection")

if __name__=="__main__":
    p=argparse.ArgumentParser();p.add_argument("input",nargs="?");a=p.parse_args()
    if a.input is None:selftest()
    else:
        with open(a.input,encoding="utf-8") as f:print(json.dumps(compute(json.load(f)),indent=2))
