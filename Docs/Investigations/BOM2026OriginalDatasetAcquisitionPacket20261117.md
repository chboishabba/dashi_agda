# BOM October 2026 audit — original-source acquisition packet

**Date:** 17 November 2026. **B0 status:** unfulfilled. **Purpose:** independently replicate the numbers in Patrick Lloyd's 1 November 2026 national raw-CDO audit, not infer wrongdoing.

## Request 1 — original researcher Patrick Lloyd

Original article: https://wattsupwiththat.com/2026/11/01/australias-duplicated-temperature-and-rainfall-data-what-the-bureau-missed/ (the author offers the full case lists). Use the article's published comments/editorial contact route. **No direct personal email address is inferred; no outreach has been sent by this repository change.**

Subject: Request for reproducibility files — 2026 Australian CDO historical revision and copied-streak audit

Dear Patrick Lloyd,

We are independently checking the numerical findings in your 1 November 2026 report, with attribution to you and to the original data publisher, BOM. Could you please supply the following unchanged research products, or an accessible signed/archive download:

1. **May 2026 original downloads** and **29–30 October 2026 original downloads**, ideally the native CDO `IDCJAC0010` / `IDCJAC0011` temperature and `IDCJAC0009` rainfall CSVs, unmodified since collection. A file inventory with timestamps, download URLs/product code, station identifiers, coverage and file hashes is ideal.
2. The **complete 44-temperature-stretch** manifest (all date-pair boundaries, original station numbers, tmin/tmax, length, comparison precision, missing-data handling) and the **32 still published** subset.
3. The **593 temperature observation removals** original station/day/variable listing, with before and after quality/accumulation states (including Sydney's 515, Charleville's 56, and 22 recent 2025/26 changes), plus the one newly added Sydney 25 June 1865 maximum 0.0°C case.
4. The **1,337 rainfall-candidate** manifest with 61,877 matched days and 13,964 wet days, including exact/gapped matching definitions, minimum wet-day support, null-control calibration, handling of multi-day accumulation, source direction and nearest-neighbour checks.
5. The **1,649 cross-station pairs / 47 distant pairs** and **22-station multi-year displacement** case sheets, station aliases, coordinates and source-year versus destination-year interpretation.
6. Original analysis code, dependencies, random seeds, comparison thresholds, candidate de-duplication, and any manual-adjudication notes. If preserving the entire corpus is impractical, the 066062 and 044022/044021 original snapshot pairs plus a manifest for all other files would let us independently start with the reported 571 historical removals.

We will publish source/algorithm manifests and either matching receipts or precise discrepancies. A verified numerical match would not by itself establish original-ledger copying, cause, climate-trend impact or deliberate manipulation.

Thank you.

## Request 2 — BOM Climate Data Services

Official data-service contact (check current public details before sending): `climatedata@bom.gov.au` — https://www.bom.gov.au/climate/maps/rainfall/

Subject: Reproducible ADAM/CDO version snapshots and historical daily-data correction ledger — May to October 2026

Dear Climate Data Services,

We are independently auditing the provenance of publicly disseminated daily station observations, not asking the Bureau to change its published ACORN-SAT trend assessment.

Could you please provide or identify:
- Exportable **as-published May 2026** and **as-published 29–30 October 2026** CDO daily observation snapshots (including product/physical station/source dates, original row quality and accumulation metadata), at minimum daily maximum/minimum for Sydney Observatory Hill 066062 and Charleville historical Post Office 044022 and Aero 044021;
- a **machine-readable ADAM/CDO change ledger** of all affected station-date-variable values before/after the 19 October update, with identifiers indicating removal, blanking, correction, original-ledger restoration and public-release provenance;
- checksums or immutable archive revision identifiers and documented complete date/variable coverage, so we can distinguish a removed observation from an unavailable download;
- the historical station provenance and 1910/1914/1935/1943 paper register references needed for proper observation authentication;
- a specification of exactly which raw inputs, homogenisation code/version, site combination rules and adjustments support the Bureau's claim of negligible national-trend impact.

If the data are only available on request, please specify applicable access, licensing and cost conditions. We will preserve the distinction between public raw data, underlying manuscript originals and ACORN-SAT derived records.

Thank you.

## Before running a national comparison

- **Never** overwrite the acquired original bytes. Calculate SHA256 immediately, preserving URL, product code, capture timestamp and independent archive provenance separately.
- Require a complete station/product/year inventory for **both** snapshots. A file missing from either capture is *not* hundreds of proven removed observations.
- Retain distinct original objects: source observation, digitised reading, quality flag, accumulation span, station site lineage and derived climate product.
- Run `scripts/bom_cdo_native_revision_audit.py` only on verified matching native CDO pairs; inspect per-value differences and source-date coverage before promoting any numeric target match to historical reproduction.
- The comparator's reported `pre2000_target_matched` is a **numeric-only** check against the author's report, not independent archive certification.
- 44 / 978 and 1,337 / 61,877 require the original **candidate definitions**, especially non-contiguous rainfall matches; never infer absence from the current 12-day contiguous-only scanner.
- For historical losses, separate blanking, calendar row disappearance, numerical changes, and quality/accumulation metadata revisions. Require both tmax and tmin station totals (regression corrected 17 Nov).

## Exact source ledger

| Source | Provenance available now | Missing item |
|---|---|---|
| Lloyd, 1 Nov 2026 original article | Published methodology narrative and claim counts | Original complete candidate lists, scripts, full 2026 station dumps |
| BOM, 22–26 Oct statement | Institution's statement and narrow ACORN-SAT affected population | Externally retrievable before/after corrections file and release-specific annual trend counterfactual |
| ABC Media Watch 26 Oct original-party reply and claimant exhibits | Cited Sydney 1910 / 1935 / 1943 mini-tables | Independent paper original and national source coverage |
| ANU, 2017 COMP1730 project | Archived **older** Sydney rain CSV link and native-format description | Locally acquired bytes; historical temperature pair; any claim that it is May/Oct 2026 |
| dashi_agda PR #1251 | Existing BOM governance audit, bounded sensitivity tests | Kernel/merge check and empirical 2026 corpus |
| dashi_agda PR #1525 | Native CSV compare and source-bounded tests | Authentic national input data, acceptance conditions |

**Request status:** drafted inside repository, **not sent**. No author response or official source release is claimed. Physical records and historical 2026 exports remain B0/B2 original-evidence gates.
