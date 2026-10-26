# 26 October 2026 — NOAA two-site daily/hourly and causal identifiability max-cut

**Owner:** draft [DASHI PR #1242](https://github.com/chboishabba/dashi_agda/pull/1242), extending the existing canonical [Pareto](psychotronics-pareto-current.md), [two-station NOAA checker](../../scripts/check_psychotronics_ellsworth_spatial_1953.py), and [revisable evidence receipt](../receipts/PsychotronicsEllsworthRevisableSourceWorld20261026.json). Original meteorological records and schema are NOAA/NCEI works; the original 1954 historical narrative is Wilhelm Reich's; this synthetic mathematical and case-specific integration is attributed to Johl Brown with OpenAI ChatGPT assistance. Neither original authorship nor scientific authority transfers via citation.

## Original source facts and custodial distinction

Two different **physical gauges** in a shared NOAA GHCN-Daily custodial archive, not two independent experimental confirmations of an extraordinary intervention:

| 1953 day | Bangor USW00014606 | Bar Harbor 3 NW USC00170371 |
|---|---:|---:|
| July 6 | 66 | 0 |
| July 7 | 193 | 130 |
| July 8 | 46 | 0 |
| 6–8 sum (tenths mm) | **305** | **130** |
| Sum (mm) | **30.5** | **13.0** |

Difference **17.5 mm** over three days. Historical date-bin reporting *cutoffs* are not established, so Bar Harbor's zero on July 6 cannot be equated with "no rain near Ellsworth at 22:00". Neither gauge is at the Graham Lake apparatus, and neither establishes an intervention effect. Original publisher URLs: [Bangor](https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USW00014606.dly), [Bar Harbor](https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USC00170371.dly), [NOAA field dictionary](https://www.ncei.noaa.gov/pub/data/ghcn/daily/readme.txt), [NOAA GHCN overview](https://www.ncei.noaa.gov/products/land-based-station/global-historical-climatology-network-daily). Original source month-lines are **publisher-web-transcribed** with flags, but **full original remote file-byte/historical clock receipt has not been authenticated**.

## Two exact, distinct, synthetic obstructions

1. **Daily-to-hourly collision.** A positive integer 24-bin daily total d admits two distinct nonnegative synthetic hourly vectors, one assigning d to hour 1, the other assigning d to hour 23. Their totals agree exactly, so the daily total cannot identify the rainfall hour. This proves noninjectivity even under a *stronger-than-evidence* midnight-to-midnight bucket assumption. Those hourly distributions are constructed counterexamples, NOT reconstructed 1953 meteorology.
2. **Treatment counterfactual collision.** Even stipulating (without claiming evidence) that the Ellsworth treated-site outcome was rain, Y(1)=1, two potential-outcome worlds (Y(0),Y(1))=(0,1) and (1,1) agree on the treated observation but have treatment effects 1 and 0. A documented onset would address timing, not by itself weather-causality identification. These are *synthetic worlds*, not estimates.

Implementation: [exact case-specific checker](../../scripts/check_psychotronics_daily_to_hourly_nogo_20261026.py), [seven focused regression cases](../../tests/test_psychotronics_daily_to_hourly_nogo_20261026.py). Both consume existing spatial/269-character source parser and revisable-source-world machinery instead of defining another ontology or importing unmerged siblings.

## Revisable provenance (source correction does not turn unknown into false)

- Withdrawing Bangor observation P1-63 reopens Bangor values plus the **two-gauge** comparison, preserving Bar Harbor values.
- Withdrawing Bar Harbor observation P1-71 reopens Bar Harbor and the comparison, preserving Bangor.
- Withdrawing shared NOAA units/schema P1-68 reopens both interpreted totals, but does not rewrite Reich's separate authored statement.
- Withdrawing Reich's author report P1-48 reopens his reported operation and onset, while preserving both NOAA station observations.
- Every change leaves the unobserved treatment counterfactual and claimed weather-causality **unpaid**; no positive or negative physical conclusion follows. Reuses existing ledger P1-63/67/68/71/72 and E111–E114; **no duplicated records**.

## Highest-information next documentary payments (Pareto/Ibrahim/snowball)

**Additional original-paper custody lead, not a dated-chart receipt:** University of Arkansas Special Collections catalogues [United States Weather Bureau: Daily Weather Map Collection MC 1268, Box 32, year 1953](https://uark.as.atlas-sys.com/repositories/2/archival_objects/21730). The archive expressly says its collection is incomplete, so the presence of 1953 material does **not** establish that 6–8 July 1953 sheets are actually in Box 32. NOAA remains the primary digital first-party chart route; the physical collection is a documentary fallback, not independent evidence of a storm or a weather-modification effect.

**A1:** original hourly or observation-clock records at the Ellsworth/Graham Lake area, if extant, with station provenance. **A2:** the [NOAA original U.S. Daily Weather Maps archive](https://library.noaa.gov/weather-climate/daily-weather-maps) and [Northern Hemisphere synoptic map archive](https://library.noaa.gov/weather-climate/synoptic-map) cover 1953. Catalogue availability is **verified**; the actual 6–8 July 1953 chart images/forecast interpretations are **not yet inspected**. Obtain pages and date/time legends before claiming an incoming front or forecast failure. **B:** the original July 8 Ellsworth American and July 24 Anthony R. Shannon Bangor Daily News newspaper pages, with possible Orgone Institute dependence preserved. **Separate branches:** original Gentry/RVML speech and Flanagan correspondence/coil plan; original Rodin 2013/2024 acquisition chain and full 2019 Saikia reference-24 comparison. Do not substitute more same-provider nearby gauge readings for those missing original objects.

Latest sibling inspiration: [#1268 revisable roots](https://github.com/chboishabba/dashi_agda/pull/1268), [#1266 consumer collision](https://github.com/chboishabba/dashi_agda/pull/1266), [#1267 severe inquiry](https://github.com/chboishabba/dashi_agda/pull/1267), [#1263 causal source/target](https://github.com/chboishabba/dashi_agda/pull/1263), and stacked child [#1252 Hardt steelman](https://github.com/chboishabba/dashi_agda/pull/1252). **Methodological reuse only:** no unmerged sibling imported. A paper archive/catalogue or secondary copy is not an original measurement, a citation is not independent corroboration, and a mathematical obstruction is not a kernel-verified Agda physical theorem.

## Exact-head commands / unverified execution

From repository root:

- python3 scripts/check_psychotronics_ellsworth_spatial_1953.py --self-test
- python3 scripts/check_psychotronics_revisable_sources_20261026.py --self-test
- python3 scripts/check_psychotronics_daily_to_hourly_nogo_20261026.py --self-test
- python3 -m unittest discover -s tests -p test_psychotronics_daily_to_hourly_nogo_20261026.py -v

These are the exact execution instructions, **not claimed as executed**. CI and Agda kernel not run. No original hourly archive, counterfactual weather experiment, psi/medical/quantum result or authenticated original full NOAA dataset bytes are claimed.
