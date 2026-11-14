#!/usr/bin/env python3
"""KSW668 empirical-source replay: author measurements != DASHI derived numbers.

Acquisition source:
    Maarten Blaauw / rintcal postbomb_SH1-2.14C (GPL >= 2);
    original calibration Hua et al. 2021 DOI 10.1017/RDC.2021.95.
Only a source-pinned excerpt and statistics are committed, not the raw 70-row file.

Usage:
    python3 scripts/ksw668_empirical_acquisition.py
        [--curve PATH] [--no-download] [--out /tmp/ksw_empirical_replay.json]

When offline, --curve points to the unchanged upstream data file.
Full curve is SHA-1 Git-blob checked before use.
"""
from __future__ import annotations
import argparse
from decimal import Decimal, getcontext
import hashlib
import json
import math
from pathlib import Path
from urllib.request import urlopen

getcontext().prec = 45
SOURCE_URL = ("https://raw.githubusercontent.com/Maarten14C/rintcal/master/"
              "inst/extdata/postbomb_SH1-2.14C")
ROOT = Path(__file__).resolve().parent.parent
MANIFEST = ROOT / "Artifacts/ksw668/empirical_primary_acquisition_20261114.json"


def git_blob_sha1(raw: bytes) -> str:
    return hashlib.sha1(b"blob " + str(len(raw)).encode() + b"\0" + raw).hexdigest()


def read_source_bytes(path: str | None, no_download: bool) -> bytes | None:
    if path:
        return Path(path).read_bytes()
    if no_download:
        return None
    with urlopen(SOURCE_URL, timeout=30) as response:
        return response.read()


def checked_source_rows(raw: bytes, provenance: dict) -> list[dict]:
    observed_sha = git_blob_sha1(raw)
    expected_sha = provenance["retrieved_blob_sha1"]
    if observed_sha != expected_sha:
        raise AssertionError(f"source blob changed: {observed_sha}, pinned {expected_sha}")
    annual = []
    for line in raw.decode("utf-8").splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        parts = line.split()
        if len(parts) != 3:
            raise AssertionError(f"bad source row: {line!r}")
        bp, age, age_sd = [Decimal(q) for q in parts]
        year = Decimal(1950) - bp
        if year != int(year):
            raise AssertionError(f"not an annual year: {year}")
        if age_sd < 0:
            raise AssertionError("negative source uncertainty")
        f14c = math.exp(-float(age) / 8033)
        annual.append({
            "calendar_year": int(year),
            "cal_BP": int(bp),
            "radiocarbon_age_BP": int(age),
            "sigma_age_BP": int(age_sd),
            "fraction_modern": round(f14c, 8),
            "sigma_fraction_modern": round(f14c * float(age_sd) / 8033, 8),
        })
    assert len(annual) == provenance["rows_read_live"] == 70
    assert min(x["calendar_year"] for x in annual) == 1950
    assert max(x["calendar_year"] for x in annual) == 2019
    selected = {r["calendar_year"]: r for r in provenance["selected_annual_source_rows"]}
    for row in annual:
        if row["calendar_year"] in selected:
            assert row == selected[row["calendar_year"]], row
    return sorted(annual, key=lambda r: r["calendar_year"])


def check_neutron_fit(paper: dict) -> list[dict]:
    fit = paper["fitted_powerlaw"]
    A, sa, B, sb, rho = [
        float(fit[k]) for k in ("A_barn", "sigma_A_barn", "B", "sigma_B", "rho_AB")
    ]
    if not -1 <= rho <= 1:
        raise AssertionError("covariance correlation invalid")
    table = []
    for item in paper["source_fit_grid"]:
        E = float(item["energy_eV"])
        sigma = A * E**B
        lnE = math.log(E)
        cov_var = ((sa/A)**2 + (lnE*sb)**2 + 2*lnE*rho*(sa/A)*sb)
        if cov_var < 0:
            raise AssertionError("negative fit covariance variance")
        sd = sigma * math.sqrt(cov_var)
        assert abs(sigma - item["fit_barn"]) < 5e-6
        assert abs(sd - item["fit_sigma_only_barn"]) < 5e-6
        table.append({"energy_eV": E, "fit_barn": round(sigma, 6),
                      "fit_only_uncertainty_barn": round(sd, 6)})
    thermal_fit = next(r for r in table if r["energy_eV"] == 0.0253)
    assert abs(paper["thermal_measured_barn"] - thermal_fit["fit_barn"]) > .05, \
        "source fit/thermal discrepancy unexpectedly vanished"
    return table


def check_biological_trial(pigeon: dict) -> dict:
    ncontrol = pigeon["n_control"]
    ndepleted = pigeon["n_depleted"]
    control_success = pigeon["control_homed_same_day"]
    depleted_success = pigeon["depleted_homed_same_day"]
    assert (ncontrol, ndepleted, control_success, depleted_success) == (16, 18, 16, 0)
    # Fisher hypergeometric, right-tail P(X>=16 | 16 successes of 34).
    p = 1 / math.comb(34, 16)
    assert abs(p - pigeon["single_tail_fisher_hypergeometric_p"]) < 1e-18
    lowcontrol = (0.025)**(1/16)
    uptreated = 1 - (0.025)**(1/18)
    rd_lower = lowcontrol - uptreated
    assert abs(rd_lower - pigeon[
        "one_sided_marginal_95_percent_clopper_pearson_conservative_lower_RD"]) < 1e-12
    return {"control_success": "16/16", "depleted_overcast_success": "0/18",
            "fisher_one_sided_p": p,
            "separately_calculated_marginal_interval_difference_lower": rd_lower,
            "condition": "source paper 19 km, overcast; distinct 70-min/same-day endpoints"}


def check_environment(paper: dict, ambient: dict) -> dict:
    reported_flux = ambient["flux_neutrons_cm2_hour"] / 3600
    rate_s = reported_flux * (1e20) * (paper["thermal_measured_barn"]*1e-24)
    assert abs(rate_s - ambient["conditional_crosssection_rate_for_1e20_targets_per_s"]) < 1e-17
    # No photon flux, tissue attenuation or location-dependent spectrum is supplied.
    return {"ambient_source_flux_neutrons_cm2_s": reported_flux,
            "conditional_uniform_thermal_R_per_second": rate_s,
            "not_biological_body_rate": True}


def main() -> None:
    parser = argparse.ArgumentParser()
    parser.add_argument("--curve", help="Unmodified upstream rintcal annual SH1-2 file")
    parser.add_argument("--no-download", action="store_true",
                        help="Skip remote download; check committed excerpt plus other receipts")
    parser.add_argument("--out", help="Write JSON execution receipt")
    args = parser.parse_args()
    manifest = json.loads(MANIFEST.read_text(encoding="utf-8"))
    data = manifest["empirical"]
    full = read_source_bytes(args.curve, args.no_download)
    annual = None if full is None else checked_source_rows(
        full, data["atmospheric_bomb_C14"])
    fitting = check_neutron_fit(data["nuclear_cross_section"])
    trial = check_biological_trial(data["pigeon_macrophage_intervention"])
    ambient = check_environment(data["nuclear_cross_section"],
                                data["measured_environmental_neutrons"])
    assert data["pigeon_macrophage_intervention"]["sequencing"]["public_SRA_experiments"] == 1
    assert not data["human_radiocarbon"]["isotope_emotion_intervention_nuclear_data_acquired"]
    receipt = {
        "schema": "dashi.ksw668.empirical-source-replay.v1",
        "full_curve_verified": annual is not None,
        "full_curve_rows": len(annual) if annual else 0,
        "source_git_blob": data["atmospheric_bomb_C14"]["retrieved_blob_sha1"],
        "peak_full_curve": max(annual, key=lambda x: x["fraction_modern"])
             if annual else data["atmospheric_bomb_C14"]["peak_source_row"],
        "neutron_fitted_grid": fitting,
        "pigeon_intervention_summary": trial,
        "measured_external_environment_conditional_model": ambient,
        "source_status": "author measurements plus bounded derived computations",
        "not_observed": ["same-person emotion perturbation 14C production",
                         "human body neutron spectrum and biological source rate",
                         "pigeon raw GPS tracks", "same-metric KK transport"],
    }
    result = json.dumps(receipt, indent=2, sort_keys=True) + "\n"
    if args.out:
        Path(args.out).write_text(result, encoding="utf-8")
    print(result)


if __name__ == "__main__":
    main()
