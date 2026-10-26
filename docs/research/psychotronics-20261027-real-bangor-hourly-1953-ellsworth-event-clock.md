# 27 October 2026 — original 1953 Bangor hourly data: actual 22:00 Ellsworth-claim clock coincidence (no causal promotion)

**Most important update to PR #1242:** The user supplied the actual NOAA-converted Bangor Global Hourly 1953 station-year CSV `72607114606.csv`. This **pays 1953 hourly observational CONTENT** previously categorised unpaid, though the actual publisher's S3 object-byte digest and NOAA legacy gzip remain unacquired. **Do not repeat old status “hourly records not obtained” without distinguishing the still-missing original ISD fixed-width gzip and original publisher-authenticated CSV delivery**.

**Original authorship and custody:** 1953 USAF surface hourly observers at Bangor International Airport, with NOAA/NCEI historical source integration and conversion. The original historical Ellsworth article (8 July 1953) and subsequent original 1954 Wilhelm Reich *CORE* publication are distinct authorial source roots. **Johl Brown** directed the joined inquiry and provided the source bytes; **OpenAI ChatGPT** performed case-specific parsed-date and attribution audit. This analysis is not original weather observation, a new scientific replicate, or Reich's published research.

## 1. Direct uploaded file custody — real data, local digest only

- User-supplied file: `72607114606.csv`, **2,724,610 bytes**, SHA-256 **`2a3b048d620b320fb8d1cf548d4eb06fb2c49821faa54c4cc7f708649cdca9bd`** (computed directly in this runtime).
- Original embedded `STATION=72607114606`, station name **BANGOR INTERNATIONAL AIRPORT, ME US**, lat `44.7978`, lon `-68.8185`, elevation `45.1 m`; **8760 rows and distinct UTC hour keys** from `1953-01-01T00:00:00` to `1953-12-31T23:00:00` (entire non-leap year).
- UTC dates 5–9 July each have **24 rows** (120 total), `SOURCE=4`, `QUALITY_CONTROL=V020`. NOAA original *ISD Format Document*, **PDF page 4 (printed 5)**, says source `4` is USAF surface hourly; `DATE`/`TIME` are UTC. Original document PDF pages 12–13 give AA1 precipitation period/depth/QC; PDF page 105 gives MW manual present-weather code 80/81; page 106 gives quality code `1` meaning pass.
- The source year and 1953 station family correspond exactly to the source object that previously had only a verified directory listing. **This is an actual user-supplied converted CSV**, not a downloaded raw original-format `726071-14606-1953.gz`; retain those as different physical format deliveries of potentially overlapping originals. The upload path is **not** proof of full NOAA remote-file custody or its authoritative publisher hash.

## 2. The decisive event-hour observation, with separate timestamps and roles

| Observed UTC hour | Local `America/New_York` 1953 EDT | Bangor manual codes (original CSV) | NOAA original-code interpretation |
|---|---|---|---|
| 6 Jul 19:00 UTC | 6 Jul 15:00 EDT | `MW1=00,1` | no reported precip; only cloud status in that hour |
| **7 Jul 02:00 UTC** | **6 Jul 22:00 EDT** | **`MW1=80,1`** | **slight rain showers at Bangor at observation; QC passed** |
| 7 Jul 04:00 UTC | 7 Jul 00:00 EDT | `MW1=81,1` | moderate/heavy rain showers |
| 7 Jul 05:00 UTC | 7 Jul 01:00 EDT | `MW1=81,1` | moderate/heavy rain showers |
| 7 Jul 06:00 UTC | 7 Jul 02:00 EDT | `MW1=17,1;MW2=80,1;MW3=95,1` | mixed thunderstorm/precip descriptors, **not all simply one phenomenon** |
| 7 Jul 07:00 UTC | 7 Jul 03:00 EDT | `MW1=80,1` | slight rain showers |
| 7 Jul 11:00 UTC | 7 Jul 07:00 EDT | `MW1=45,1; MW2=51,1` | fog plus slight continuous drizzle |
| 7 Jul 12:00 UTC | 7 Jul 08:00 EDT | `MW1=45,1; MW2=51,1` | fog plus slight continuous drizzle |

**Maine's original historical clock:** independent date-specific historic DST calendar says **Maine** observed daylight time from **26 April to 27 September 1953**, so July observations use UTC−4 rather than UTC−5. IANA `America/New_York` historical tzdata independently yields `1953-07-07T02:00Z` → `1953-07-06T22:00-04:00`. Sources: [historical Maine DST for 1953](https://www.timeanddate.com/time/change/usa?year=1953), [IANA historical time-zone data](https://data.iana.org/time-zones/tz-link.html).

**Historical source-root join:** Original *Ellsworth American* dated **8 July 1953**, as printed in **Wilhelm Reich's 1954 *CORE* volume VI**, reports rain at the Ellsworth operation region at approximately **22:00 Monday 6 July**, followed by a steadier rain around midnight. The above Bangor **observed 22:00** weather code is a genuine *clock-time agreement for precipitation in the wider area*, independent of the Reich written account as a reporting lineage, but **Bangor is not the Ellsworth site**. An observed rain shower at 22:00 does **NOT** date the actual *onset* of rain to 22:00: prior hourly `MW1=00` codes are not a rain gauge reporting first drop, and a shower could start before observation. **It does NOT verify the source's account of intervention efficacy**. The historical source is a 1954 original-author republication of earlier newspaper content; the original July 8 original newspaper scan was not directly retrieved in this pass.

**Important code caveat:** at `1953-07-07T06:00:00Z`, the same record carries `MW1=17` (thunderstorm without precipitation at observation) alongside `MW2=80` and `MW3=95` (rain shower/thunderstorm with rain), all code quality `1`. These are separate reported manual elements with a complex conjunction; do NOT collapse them into an onset or trivial “all 3 independently confirm rain” claim. Preserving the raw fields prevents an unwarranted certainty upgrade.

## 3. AA1 accumulation, GHCN-Daily measurement-denominator audit

At **12:00 UTC / 08:00 EDT**, the CSV's `AA1` groups explicitly represent **24-hour rainfall accumulation**, not rain in the reporting hour.

| July UTC date | Raw hourly CSV `AA1` at 12Z | Converted 24h mm | Prior original-publisher transcribed GHCN-Daily July 1953 mm | CSV−GHCNd mm |
|---|---|---:|---:|---:|
| 5 | `24,0000,9,1` | 0.0 | 0.0 | 0.0 |
| 6 | `24,0070,9,1` | 7.0 | 6.6 | +0.4 |
| 7 | `24,0190,9,1` | 19.0 | 19.3 | −0.3 |
| 8 | `24,0050,9,1` | 5.0 | 4.6 | +0.4 |
| 9 | `24,0070,9,1` | 7.0 | 7.4 | −0.4 |

Original prior `USW00014606` **269-column** `PRCP` NOAA publisher web-transcript remains in [existing station source receipt](../receipts/NOAABangor1953JulyPRCPWebExcerpt20261026.txt). Corresponding nearest-whole-mm agreement strongly suggests differently quantised versions of related station reports; **no proved identical raw instrument source** without provenance audit, and certainly not two independent weather-modification experiments. `AA1` 4th `1` means passes QC; condition code `9` is **missing/N/A**, not an added 9 mm nor a failed QC. Values don't allocate the 19 mm among hours within the preceding 24h or prove Ellsworth onset.

## 4. Observations, adversarial hypothesis and limits

**Paid:** real 1953 hourly Bangor CSV content; real 1953 5–9 July hourly station coverage; real first rain-weather manual code at 22:00 Maine daylight time on July 6; original NOAA-code interpretation/QC; genuine 24h AA1 amounts and a numerical daily source-family concordance; source-specific SHA. The exact [real-upload Python replay](../../scripts/check_psychotronics_1953_actual_bangor_replay.py) was actually executed on the user-supplied 2.7MB CSV, emitted 8760 observations with first valid manual rain code at `1953-07-07T02:00Z`, and its locally executed source Git blob **`586b5dc3a13d320b508d21aa0b4e3d16c1ded58c`** equals the blob on this GitHub PR. Python compilation **PASS**. This is **real historical data replay**, unlike the earlier 33 mock regression tests.

**Unpaid:** original NOAA remotely independently authenticated CSV ETag/byte hash; archival original fixed-width 1953 gzip; observer logs at exact Graham Lake Dam/Ellsworth coordinates; Ellsworth 1953 independent rain-onset hour; original 6–7 July 1953 Weather Bureau synoptic original forecast/chart page; a credible counterfactual with operation unperformed; potential atmospheric physics demonstration. Don't infer a device altered rainfall merely because the measured nearby-station first coded shower timestamp coincides with an original claim.

This incident is an excellent adversarial positive-control case for the programme: **an original-sounding anomalous story predicts a factual event that is supported by independent nearby weather data, while its proposed causal mechanism remains unsupported**. The original inquiry into all 18 devices/screenshots continues via [canonical phase/deliverables](psychotronics-original-inquiry-phase-gates-deliverables-20261027.md); this is one source-measurement leaf, not completion of P2/P3/P4 experimental and formal proof.
