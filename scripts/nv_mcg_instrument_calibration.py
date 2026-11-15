#!/usr/bin/env python3
"""Source-gated CW NV ODMR fitting + measured magnetic sensitivity.

Reads actual instrument CSV: frequency_hz,signal (ODMR); for noise
time_s,signal (same electrical/optical output unit). Optional separately
MEASURED signal-per-tesla slope overrides CW static derivative.

Example:
 python scripts/nv_mcg_instrument_calibration.py --odmr odmr.csv \
   --noise noise.csv --instrument ZAQuant --output result.json

The fitted slope from an unmodulated Lorentzian must NOT be used as the
system calibration of a lock-in-modulated sensor without a separately
measured signal-versus-field transfer function.
"""
import argparse,csv,json,math,pathlib
import numpy as np
from scipy.optimize import least_squares
from scipy.signal import welch

SOURCES={"JGU":{"reported_pt_root_hz":13.0,"band_hz":[20,30],"protocol":"zero-bias magnetic field modulation"},
         "ZAQuant":{"reported_pt_root_hz":7.0,"band_hz":None,"protocol":"MW frequency modulation"},
         "Q.ANT":{"reported_pt_root_hz":26.0,"band_hz":None,"protocol":"MW amplitude modulation"}}
def read_csv(path,columns):
    with open(path,newline="") as f:
        records=list(csv.DictReader(f))
    if len(records)<12: raise ValueError("At least 12 observations required")
    a=np.array([[float(row[k]) for k in columns] for row in records],dtype=float)
    if not np.isfinite(a).all():raise ValueError("Nonfinite measurement")
    if not np.all(np.diff(a[:,0])>0):raise ValueError("First coordinate must increase")
    return a
def lorentzian(f,baseline,depth,center,hwhm):
    return baseline-depth*hwhm**2/((f-center)**2+hwhm**2)
def fit_odmr(rows):
    f,y=rows.T
    baseline=float(np.quantile(y,.90));depth=max(float(baseline-np.min(y)),float(np.std(y))*.01,1e-12)
    width=max(float((f[-1]-f[0])/20),1e-12)
    scale=max(float(np.std(y)),1e-12)
    def residual(p):return (lorentzian(f,*p)-y)/scale
    fit=least_squares(residual,[baseline,depth,float(f[np.argmin(y)]),width],
         bounds=([-np.inf,0,f[0],np.finfo(float).tiny],[np.inf,np.inf,f[-1],f[-1]-f[0]]),
         max_nfev=15000)
    b,d,center,hwhm=map(float,fit.x)
    slope_max=9*d/(8*math.sqrt(3)*hwhm) # at +/- hwhm/sqrt(3)
    return {"baseline":b,"depth":d,"center_hz":center,"fwhm_hz":2*hwhm,
            "contrast":d/b if b>0 else None,"max_abs_dsignal_df_hz":slope_max,
            "fit_rms_signal":float(np.sqrt(np.mean((lorentzian(f,*fit.x)-y)**2))),
            "converged":bool(fit.success),"n_odmr":len(f)}
def noise_asd(rows,band,window_s):
    t,y=rows.T
    dt=float(np.median(np.diff(t)))
    if np.max(abs(np.diff(t)-dt)) > dt*.01:
        raise ValueError("Noise sample timing not uniform within 1%")
    fs=1/dt
    nperseg=min(len(y),max(32,int(fs*window_s)))
    frequency,psd=welch(y,fs=fs,nperseg=nperseg,window="hann",
                         scaling="density",detrend="constant")
    valid=(frequency>=band[0])&(frequency<=band[1])
    if not valid.any():raise ValueError("No Fourier bins in the specified noise band")
    return {"asd_median_signal_root_hz":float(np.median(np.sqrt(psd[valid]))),
            "n_noise":len(y),"fs_hz":fs,"nperseg":nperseg,
            "resolution_hz":fs/nperseg,"noise_band_hz":list(band)}
def main():
    p=argparse.ArgumentParser()
    p.add_argument("--instrument",choices=SOURCES,required=True)
    p.add_argument("--odmr",help="Measured frequency_hz,signal CSV")
    p.add_argument("--noise",help="Measured time_s,signal CSV")
    p.add_argument("--slope-signal-per-tesla",type=float,
                   help="Independently measured demodulated signal/tesla")
    p.add_argument("--band",nargs=2,type=float)
    p.add_argument("--window-s",type=float,default=1.)
    p.add_argument("--output",required=True)
    a=p.parse_args()
    if not a.odmr and not a.noise:raise SystemExit("Provide measured ODMR and/or noise")
    if a.slope_signal_per_tesla is not None and a.slope_signal_per_tesla==0:
        raise ValueError("Sensitivity slope must be nonzero")
    reference=SOURCES[a.instrument]
    report={"instrument":a.instrument,"source":"Omar et al. Sci Adv 2026 doi:10.1126/sciadv.aeg5281",
            "publication_anchor":reference,"measured_data_provided":[]}
    if a.odmr:
        report["odmr"]=fit_odmr(read_csv(a.odmr,["frequency_hz","signal"]))
        report["measured_data_provided"].append("ODMR")
    if a.noise:
        band=a.band or reference["band_hz"]
        if band is None:raise ValueError("Explicit --band required for this instrument")
        if band[0]<0 or band[0]>=band[1] or a.window_s<=0:raise ValueError("Invalid band/window")
        report["noise"]=noise_asd(read_csv(a.noise,["time_s","signal"]),band,a.window_s)
        report["measured_data_provided"].append("noise")
    if a.noise and a.slope_signal_per_tesla is not None:
        measured=report["noise"]["asd_median_signal_root_hz"]/abs(a.slope_signal_per_tesla)*1e12
        report["calibrated_system_pt_root_hz"]=measured
        report["ratio_to_published_anchor"]=measured/reference["reported_pt_root_hz"]
        report["calibration_basis"]="Measured modulated signal-to-field slope + measured ASD"
    else:
        report["calibrated_system_pt_root_hz"]=None
        report["missing"]="Measured noise trace AND independent field-to-demodulated-output slope"
    pathlib.Path(a.output).write_text(json.dumps(report,indent=2,allow_nan=False)+"\n")
    print(json.dumps(report,indent=2,allow_nan=False))
if __name__=="__main__":main()
