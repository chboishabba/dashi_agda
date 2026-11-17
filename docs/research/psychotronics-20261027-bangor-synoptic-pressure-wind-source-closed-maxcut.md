# 27 October 2026 — 1953 Ellsworth claim: real Bangor pressure / wind / cloud rival-model audit

**Purpose / original inquiry:** Extend the 18-screenshot Succor Punch/coil/device evidence investigation by testing an independent meteorological discriminator for the historical 6 July 1953 *Ellsworth* cloudbuster narrative. This is a **source-bound contextual audit** of a single original Bangor weather-observer stream, **not** causal confirmation or refutation of Reich's operation. It is an adjunct to the [existing verified real-data 22:00 weather-code cut](psychotronics-20261027-real-bangor-hourly-1953-ellsworth-event-clock.md) and [original 18-still P0–P5 roadmap](psychotronics-original-inquiry-phase-gates-deliverables-20261027.md).

**Original attribution:** NOAA/NCEI ISD and USAF historic Bangor Airport surface observers own the weather measurements and 1953/2026 archive/conversion process; original *Ellsworth American* (8 July 1953) and Wilhelm Reich (1954 *CORE* original authored protocol) own their respective published statements. The 1954 republication does not become an additional independent 1953 witness. Research direction, source reconciliation and question selection Johl Brown; assistant-generated case-specific decoder, tests and report OpenAI ChatGPT assistance. No new measurements or authorship claimed over original weather observations. Citation: [original NOAA/USAF 2018 ISD Format Document, Federal Climate Complex](https://www.ncei.noaa.gov/pub/data/noaa/isd-format-document.pdf) printed pages 5, 8–13; [NOAA ISD overview](https://www.ncei.noaa.gov/products/land-based-station/integrated-surface-database).

## What exactly was observed and tested

User-provided original NOAA-converted station-year CSV **\`72607114606.csv\`**, SHA-256 **\`2a3b048d620b320fb8d1cf548d4eb06fb2c49821faa54c4cc7f708649cdca9bd\`**, 8760 unique UTC station-hours, all hours present July 5–9. This local original input is not a NOAA publisher-authenticated *remote* S3 checksum or the independently acquired original fixed-width ISD gzip. Reused existing **P1-85** source role and root \`noaa-isd-hourly\`; **no new source role, observer, independent test or experiment added**.

New exact [source-written Python analysis](../../scripts/check_psychotronics_bangor_1953_synoptic_null.py), Git blob \`c976b9c33db99f5fe696ddd01a9f8c5d0b710fcb\`, checks SHA, station, UTC date uniqueness, source literal MW1 \`80,1\`, and QC of SLP, WND, CIG; handles missing/sentinel \`SLP=99999\`, \`WND=999\`, wind speed \`9999\`, and **CIG=22000 as unlimited, not a 22,000-metre measured cloud base**. All computations use original NOAA-documented scale: sea-level pressure in **tenths hPa**, wind direction in degrees clockwise **from true north**, wind speed in **tenths m/s**, ceiling height in metres AGL. QC \`1\` means passed all checks for each used field. Yearly station source flag \`4\` means USAF surface hourly observation; weather codes describe the reporting hour, not the minute precipitation began.

### Operation time versus available hourly station observations

Original Reich's published account reports **Graham Lake Dam near Ellsworth** operation from **10:45 to 11:52 EDT on 6 July 1953**, converted to **14:45–15:52 UTC** using historical Maine civil time. Bangor Airport is a different location.

| Bangor observation UTC | Maine civil time | SLP (hPa) | Wind direction from true N | Speed (m/s) | Reported cloud ceiling |
|---|---|---:|---:|---:|---:|
| Jul 6 12:00 | Jul 6 08:00 | 1016.6 | 200° | 7.2 | Unlimited |
| Jul 6 14:00 | Jul 6 10:00 | 1015.5 | 200° | 6.7 | 5,400 m AGL |
| Jul 6 15:00 | Jul 6 11:00 | 1015.5 | 200° | 7.7 | 6,000 m AGL |
| Jul 6 16:00 | Jul 6 12:00 | 1015.2 | 200° | 6.2 | 7,500 m AGL |
| Jul 6 18:00 | Jul 6 14:00 | 1013.3 | 200° | 7.7 | 7,500 m AGL |
| Jul 6 20:00 | Jul 6 16:00 | 1011.9 | 200° | 7.7 | 7,500 m AGL |
| Jul 7 00:00 | Jul 6 20:00 | 1010.2 | 200° | 6.7 | 2,400 m AGL |
| **Jul 7 02:00** | **Jul 6 22:00** | **1008.8** | **200°** | **8.2** | **1,800 m AGL; MW1=80 slight rain showers** |
| Jul 7 04:00 | Jul 7 00:00 | 1006.8 | 200° | 7.2 | 1,500 m AGL |
| Jul 7 08:00 | Jul 7 04:00 | 1004.4 | 200° | 1.5 | 600 m AGL |

**High-value original distinction:** while the 1954 Reich claim reports a **SW→SE wind shift during the operation**, the actual *Bangor* station's hourly wind direction shows **200° at 14:00, 15:00 and 16:00 UTC**, bracketing the claimed 14:45–15:52 UTC intervention. No corresponding change is present **at Bangor within those hourly samples**. This **does not test** the wind shift at geographically different Graham Lake, and cannot disprove the site-specific original account. Likewise the pre-existing clouds and pressure trend at Bangor cannot be mapped without regional observations to the purported Ellsworth site.

**Quantified pressure development:** within the real quality-passing hourly records, Bangor SLP declined by **6.7 hPa** from July 6 14:00 UTC to July 7 02:00 UTC (twelve hours before the first reported manual Bangor showers, which may have begun earlier). The **24-hour** preceding change was **−9.5 hPa**, and the final six hours preceding that recorded shower was **−3.1 hPa**. During operation-bracketing **14:00→16:00 UTC** Bangor pressure changed **−0.3 hPa**, not zero; after the operation the pressure continued falling. This is genuine weather development and a **conventional atmospheric alternative worth investigating**, not proof of any particular frontal passage, a predictive forecast, any hidden physical mechanism or a device/no-device counterfactual.

### Same-station July 1953 descriptive reference, not an intervention p-value

A direct exact computation across **all 744 hourly endpoints in July** compares each QC-passing sea-level-pressure value with the observation **twelve hours earlier**, including the June→July start-hour boundary where appropriate. Of 744 eligible pairs, **46** have a 12-hour pressure decline at least as large as the **−6.7 hPa** event-hour value: a **descriptive 46/744 ≈ 6.18% of overlapping window endpoints**. Adjacent windows overlap by eleven of twelve hours, are strongly dependent and include arbitrary rain/dry meteorological states; there are **not 744 independent trials, not randomized intervention/nonintervention comparisons, and not a p-value for Reich’s intervention**. The exercise is a practical data-audit comparator showing that large pressure declines occurred elsewhere that July in the same NOAA observer series without classifying their causes.

**Exact execution:** [15 source-specific local tests](../../tests/test_psychotronics_bangor_1953_synoptic_null.py), exact local/git blob \`319162a0b429be9dae85cf3b4534b8e6d771123a\`, **15/15 PASS** in the real \`scripts/\`+\`tests/\` layout; four test methods replay actual uploaded file and the others enforce original-unit/quality failures. Source script itself compiled, ran on the real uploaded file and produced a source-identified JSON evidence output. This extends (does not duplicate) the preceding 33 test suite and 8 real-replay tests; separate count carefully by test definition and data witness. The new typed Agda \`ClaimBound\` guards are **source written but not kernel typechecked**, and reuse the existing NOAA original station root rather than inventing another experiment.

## Severe competing model and evidence obligations

**Competing conventional physical model:** evolving 1953 atmospheric circulation/moisture plus surface pressure changes generates region-wide precipitation with or without a cloudbuster. An intervention claim would require discriminating this model from a device-dependent modification, not just showing rain at 22:00. We have an observed Bangor pressure time series and weather code (support for weather occurring), **not an independent weather-system reconstruction or specific forecast**.

**Unpaid decisive originals:**
1. Exact **July 6–7, 1953 original US Weather Bureau Daily Weather Maps** / forecast narratives and isobars/fronts. The original [NOAA Library historical map catalogue](https://library.noaa.gov/weather-climate/daily-weather-maps) confirms a searchable daily 1871–1968 collection and exact-date search query **\`19530706\`**, **\`19530707\`**. The embedded dynamic map table did not yield the 1953 scanned original pages in the available browser. WPC's 1879+ [archive](https://www.wpc.ncep.noaa.gov/archives/web_pages/sfc/historic_sfc_archive.php) currently explicitly says its form currently only contains 1978–1979, therefore it is **not** a verified 1953 map source. A random historical May 1953 storm map from image search **must not** be used as an actual July 1953 map.
2. Original Ellsworth/Graham Lake location-matched observation or original 1953 newspaper weather reporting, with author and site/time attribution.
3. Pre-registered causal comparison and robust classical atmospheric confounders before asserting or experimentally dismissing any physical extraordinary claim.
4. Return to primary original 18-image/device scope; this is one weather branch, not a substitute for the Croft/Gentry, Rodin/ACS original SI and calibrated same-device hardware audits.

**Resulting Phase 1 status:** actual uploaded 1953 Bangor hourly observations + original-code decoding + measured conventional meteorological pretrend are **paid**. Exact Ellsworth site onset, weather-system identification, original operational causality, rare/psy/quantum/scalar physical effects and P2/P3 empirical evidence remain **unpaid**. Do not let a temporal match, falling pressure, or overlapping-window descriptive rank become proof for *or* against Reich’s device.