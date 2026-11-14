#!/usr/bin/env python3
"""C2 grounded site input -> reproducible PARMA spectrum; not a measured body flux.

Site needs measured/requested latitude/longitude, elevation, calendar date,
soil-water H fraction and ideally measured atmospheric depth. No inference
of the user's actual address or biological specimen site.

Official JAEA EXPACS/PARMA 4.19 (Nov 5, 2026) is the preferred original
source; JAEA software requires accepting its noncommercial terms.
Optional *secondary* offline implementation neptoon vPARMA4.10 ships original
coefficient tables and historical W index:
 https://www.neptoon.org/en/latest/user-guide/parma-offline/
This is NOT equivalent to JAEA's latest 4.19 or calibrated neutron dosimetry.
Offline model documented support is 0.01 to 100000 MeV; such an export
cannot constrain thermal 0.0036–1.8 eV 14N(n,p)14C; full thermal/body neutron
rates must use independently measured or validated thermal source and tissue
transport (e.g. Geant4), not zero-fill missing energy.

Output uses energy_eV,differential_flux_cm2_s_eV, as required by
ksw668_endf81_c2_law_integral.py, with full inputs and checksum receipt.
"""
import argparse,csv,hashlib,json,math
from datetime import date
from pathlib import Path

def execute(args):
    import numpy as np
    from neptoon.external.parma_python_crns import (
        bundled_neutron_model,bundled_historical_w_index,bundled_site_tables)
    from importlib.metadata import version
    model=bundled_neutron_model()
    w=bundled_historical_w_index().at(args.date)
    site=bundled_site_tables()
    rc=site.cutoff_rigidity_gv(args.latitude,args.longitude)
    depth=(args.atmospheric_depth_g_cm2 if args.atmospheric_depth_g_cm2 is not None
           else site.atmospheric_depth_g_cm2(args.altitude_m))
    energy=np.geomspace(.01,100000,args.energy_points)
    flux=np.asarray(model.neutron_spectrum(
        w_index=w,cutoff_rigidity_gv=rc,
        atmospheric_depth_g_cm2=depth,
        ground_water_fraction=args.ground_water_fraction,
        energy_mev=energy),dtype=float)
    if flux.shape!=energy.shape or not np.isfinite(flux).all() or np.any(flux<0):
        raise RuntimeError("PARMA returned invalid or unphysical spectrum")
    output=args.out
    output.parent.mkdir(parents=True,exist_ok=True)
    with output.open("w",newline="") as f:
        wr=csv.writer(f);wr.writerow(["energy_eV","differential_flux_cm2_s_eV"])
        for e,phi in zip(energy,flux):
            wr.writerow([format(e*1e6,".15g"),format(phi/1e6,".15g")])
    return {
       "status":"SECONDARY PARMA4.10 MODEL EXECUTED, not measured neutron/body flux",
       "source":"neptoon offline PARMA4.10, original JAEA coefficients; official EXPACS 4.19 separate",
       "neptoon_package_version":version("neptoon"),
       "model_source":"https://www.neptoon.org/en/latest/user-guide/parma-offline/",
       "official_JAEA_site":"https://phits.jaea.go.jp/expacs/top-eng.htm",
       "date":args.date,"latitude":args.latitude,"longitude":args.longitude,
       "altitude_m":args.altitude_m,
       "ground_water_fraction":args.ground_water_fraction,
       "atmospheric_depth_gcm2":float(depth),
       "solar_W_index":float(w),
       "geomagnetic_cutoff_rigidity_GV":float(rc),
       "spectrum_Energy_MeV":[.01,100000],
       "source_energy_points":len(energy),
       "output_source_csv":str(output),
       "output_sha256":hashlib.sha256(output.read_bytes()).hexdigest(),
       "measured_neutrons_inside_human":False,
       "thermal_0p0036_to_1p8_eV_covered":False,
       "full_N14_site_or_body_rate_established":False,
    }

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--execute",action="store_true")
    ap.add_argument("--latitude",type=float)
    ap.add_argument("--longitude",type=float)
    ap.add_argument("--altitude-m",type=float)
    ap.add_argument("--date")
    ap.add_argument("--ground-water-fraction",type=float)
    ap.add_argument("--atmospheric-depth-g-cm2",type=float)
    ap.add_argument("--energy-points",type=int,default=300)
    ap.add_argument("--out",type=Path)
    ap.add_argument("--receipt",type=Path)
    a=ap.parse_args()
    if a.execute:
        try:
            day=date.fromisoformat(a.date)
        except (TypeError,ValueError):
            ap.error("Valid ISO source calendar --date YYYY-MM-DD required")
        if day>date(2026,3,26):
            ap.error("Bundled Neptoon PARMA4.10 original solar W index ends 2026-03-26; do not extrapolate. Provide a verified external W-index extension in a separately versioned adapter.")
    if not a.execute:
        result={"status":"PLAN ONLY. No site inferred and no PARMA data generated.",
            "external_model_requires":"neptoon offline PARMA4.10 installed, or official JAEA EXPACS 4.19 used under terms",
            "required":"latitude longitude altitude-m date ground-water-fraction out",
            "thermal_14N_cross_section_not_covered_by_neptoon_example":True}
    else:
        for key in ("latitude","longitude","altitude_m","date","ground_water_fraction","out"):
            if getattr(a,key) is None:ap.error("--execute requires --"+key.replace("_","-"))
        if not (-90<=a.latitude<=90 and -180<=a.longitude<=180 and
                0<=a.ground_water_fraction<=1 and 20<=a.energy_points<=10000 and
                math.isfinite(a.altitude_m)):
            ap.error("Invalid source environment / source domain")
        result=execute(a)
    output=json.dumps(result,sort_keys=True,indent=2)+"\n"
    if a.receipt:a.receipt.write_text(output)
    print(output)

if __name__=="__main__":
    main()
