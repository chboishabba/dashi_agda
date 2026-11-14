#!/usr/bin/env python3
"""Source-scoped 14N(n,p)14C rate folding, with correlated fitted uncertainty.

Never treat the neutron spectrum as a paper citation. Provide a genuine measured
Gordon-style or author-licensed PARMA/EXPACS spectral CSV and its source
identifier; this code does NOT acquire a spectrum or run an EXPACS installation.

Input CSV columns: energy_eV,differential_flux (cm^-2 s^-1 eV^-1)
or energy_MeV,differential_flux (cm^-2 s^-1 MeV^-1).
The empirical Li et al. (2026) power fit is only valid 0.0036 <= E <= 1.8 eV:
  sigma(E) = A E**B barn;
  A=0.2706 +- 0.0074, B=-0.5103 +- 0.0050, corr(A,B)=0.993.
An incomplete energy interval produces a partial RATE only; never call it the
total human-body or full-spectrum rate. Model uncertainty != counting errors.
"""
import argparse
import csv
import json
import math
from hashlib import sha256
from pathlib import Path

E_MIN = 0.0036
E_MAX = 1.8
A, SA = 0.2706, 0.0074
B, SB, RHO = -0.5103, 0.0050, 0.993
BARN_CM2 = 1e-24
SOURCE_DOI = "10.1080/00223131.2026.2750299"


def read_spectrum(path):
    path = Path(path)
    with path.open(newline="", encoding="utf-8-sig") as handle:
        rdr = csv.DictReader(handle)
        keys = set(rdr.fieldnames or [])
        if {"energy_eV", "differential_flux"} <= keys:
            factor = 1.0
            unit = "eV"
        elif {"energy_MeV", "differential_flux"} <= keys:
            factor = 1.0e6
            unit = "MeV"
        else:
            raise ValueError("Expected energy_eV or energy_MeV and differential_flux")
        rows = [(float(row["energy_" + unit]) * factor,
                 float(row["differential_flux"]) / factor)
                for row in rdr]
    if len(rows) < 2:
        raise ValueError("At least two energy-flux samples required")
    if any(not (math.isfinite(x) and math.isfinite(f)) or x <= 0 or f < 0
           for x, f in rows):
        raise ValueError("Energy must be finite/positive; differential flux finite/nonnegative")
    if any(rows[i+1][0] <= rows[i][0] for i in range(len(rows)-1)):
        raise ValueError("Energies must be strictly increasing; do not silently sort or merge")
    return rows, unit, sha256(path.read_bytes()).hexdigest()


def interpolate(rows, e):
    for (e0, f0), (e1, f1) in zip(rows[:-1], rows[1:]):
        if e0 <= e <= e1:
            return f0 + (f1-f0)*(e-e0)/(e1-e0)
    raise ValueError("Interpolation outside source's measured/modelled energy support")


def restrict_fit_window(rows):
    lo = max(rows[0][0], E_MIN)
    hi = min(rows[-1][0], E_MAX)
    if hi <= lo:
        raise ValueError("No overlap with source-validated 0.0036–1.8 eV cross section")
    interior = [(e, f) for e, f in rows if lo < e < hi]
    return [(lo, interpolate(rows, lo))] + interior + [(hi, interpolate(rows, hi))]


def trapezoid_pair(points, func):
    return sum((e1-e0)*(f0*func(e0)+f1*func(e1))/2
               for (e0,f0),(e1,f1) in zip(points[:-1],points[1:]))


def fold(rows, target_atoms, source_name):
    if not source_name.strip():
        raise ValueError("A source for the input neutron spectrum is mandatory")
    if not (math.isfinite(target_atoms) and target_atoms >= 0):
        raise ValueError("Invalid nonnegative N14 target inventory")
    points = restrict_fit_window(rows)
    rate_weight = lambda e: A * e**B
    b_weight = lambda e: rate_weight(e)*math.log(e)
    integrated_flux = trapezoid_pair(points, lambda e:1)
    integral_weight = trapezoid_pair(points, rate_weight)
    dB_weight = trapezoid_pair(points, b_weight)
    factor = target_atoms * BARN_CM2
    rate = factor * integral_weight
    dA = rate / A
    dB = factor * dB_weight
    variance = (SA*dA)**2 + (SB*dB)**2 + 2*RHO*(SA*dA)*(SB*dB)
    if variance < -1e-24:
        raise AssertionError("Negative covariance-derived rate variance")
    return {
        "classification": "partial energy-window reaction-rate model, NOT measured human rate",
        "input_spectrum_source": source_name,
        "cross_section_original_DOI": SOURCE_DOI,
        "fit_range_eV":[E_MIN,E_MAX],
        "actual_integrated_window_eV":[points[0][0],points[-1][0]],
        "covers_entire_fit_range": points[0][0] <= E_MIN and points[-1][0] >= E_MAX,
        "input_energy_support_eV":[rows[0][0], rows[-1][0]],
        "original_input_spectrum_total_flux_cm2_s": trapezoid_pair(rows,lambda e:1),
        "used_window_flux_cm2_s": integrated_flux,
        "modelled_in_window_reactions_per_second": rate,
        "fit_covariance_only_sigma_per_second": math.sqrt(max(0.0,variance)),
        "n14_target_atoms":target_atoms,
        "method":"linear differential-flux interpolation + trapezoidal energy integration",
        "warning":"Rate outside validated 0.0036–1.8 eV is unknown, not zero; PARMA soil/albedo, geometry, attenuation and in-body flux absent unless separately measured",
    }


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--spectrum",type=Path,required=True)
    ap.add_argument("--source",required=True,help="Provenance of measured/Gordon/PARMA spectrum, URL and run settings")
    ap.add_argument("--n14-atoms",type=float,required=True)
    ap.add_argument("--out",type=Path)
    ns=ap.parse_args()
    rows,unit,digest=read_spectrum(ns.spectrum)
    receipt=fold(rows,ns.n14_atoms,ns.source)
    receipt.update({"spectrum_input_sha256":digest,"original_input_energy_unit":unit})
    result=json.dumps(receipt,sort_keys=True,indent=2)+"\n"
    if ns.out: ns.out.write_text(result)
    print(result)


if __name__=="__main__":
    main()
