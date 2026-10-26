# 26 October 2026 — original Bar Harbor GHCN station: 1953 Ellsworth regional spatial max-cut

**Scope:** PR #1242 Phase-1 original-document research, not Field Loom instrumentation or a device-effect claim. Johl Brown directs the source comparison; OpenAI ChatGPT assisted compilation/code. NOAA/NCEI and the underlying station observers retain original measurement and data-method authorship (GHCN-Daily: Menne, Durre, Vose, Gleason and Houston 2012, DOI 10.1175/JTECH-D-11-00103.1). Wilhelm Reich owns his original 1954 event claims; later reporters retain their own bylines.

## New original source and actual observation

NOAA [Bar Harbor 3 NW, ME, **USC00170371**](https://www.ncdc.noaa.gov/cdo-web/datasets/GHCND/stations/GHCND%3AUSC00170371/detail) states station 44.41667 N, −68.25° (west longitude), 34.1 m, period 1893-01-01 to 1982-08-31. Its first-party [GHCN-Daily .dly station original](https://www.ncei.noaa.gov/pub/data/ghcn/daily/all/USC00170371.dly), searchable July 1953 **line USC00170371195307PRCP**, contains 269 fixed-width characters; [official NOAA readme](https://www.ncei.noaa.gov/pub/data/ghcn/daily/readme.txt) defines 31 day records of 5-digit PRCP in tenths-mm followed by measurement, quality and source flags. This is the historical **BAR HARBOR 3 NW** gauge, **not** the similarly named later 2005 Bar Harbor Airport / WBAN:14616 (not a 1953 record) and not the post-1982 Acadia NP station. NPS independently notes a Bar Harbor climate observation tradition since 1893 (https://www.nps.gov/acad/learn/nature/historic-data-sets.htm), but this institutional narrative is NOT a second rain measurement.

The original official NOAA web text was directly read on 26 October 2026; the exact *single month* row is preserved verbatim in [source excerpt](../receipts/NOAABarHarbor1953JulyPRCPWebExcerpt20261026.txt). The full original .dly bytes were **not downloaded**, and an original publisher-file SHA is **not claimed**. A subsequent source revision could change values; the transcribed dated row is a historical read receipt, not an immutable original file.

| Day July 1953 | NOAA Bangor USW00014606 PRCP 0.1 mm | NOAA Bar Harbor 3 NW USC00170371 PRCP 0.1 mm |
|---|---:|---:|
| 5 | 0 | 0 |
| 6 | 66 | 0 |
| 7 | 193 | 130 |
| 8 | 46 | 0 |
| 9 | 74 | 10 |
| **6–8 sum** | **305 = 30.5 mm** | **130 = 13.0 mm** |

Both records have blank GHCN quality flags for these compared observations; their source flags and trace measurement flags are retained in the original excerpts. The **175 tenths-mm (17.5 mm) difference over July 6–8** demonstrates why a single Bangor gauge cannot serve as a literal Ellsworth rainfall trace, and why two stations cannot be treated as the *same* experiment. The two records are two distinguishable observation-series from **one NOAA custodial data network**, not two independently authored validations of a cloudbuster.

**Observation-time guard:** The Bar Harbor 6 July daily PRCP value is zero, and 7 July is 130 tenths-mm. Without original 1953 observer reading time, gauge assignment/cutoff, quality revisions, hourly log and regional fronts, the zeros cannot be interpreted as proof that no rain fell during the **evening** of July 6. Likewise a recorded 13.0 mm on July 7 does not pin the first rain to Reich's claimed 22:00 on July 6. Site-specific Ellsworth/Graham Lake precipitation and counterfactual weather remain unverified.

**Source-entailment guard:** (i) NOAA station rain existed somewhere in the Maine region; (ii) Wilhelm Reich's 1954 narration names an operation, afternoon timing and a weather front from the west; (iii) an 8 July Ellsworth American article was reproduced by Reich's later CORE compilation. These are different documentary objects. Co-occurrence does not identify an intervention effect, establish a false forecast, certify 22:00 local rainfall, or verify non-Maxwell/quantum/orgone weather physics.

## Actual implementation / selective revisions

- The [new exact-row two-station replay](../../scripts/check_psychotronics_ellsworth_spatial_1953.py) **imports existing** `check_psychotronics_ellsworth_1953_sources.parse_dly_record`, does not build a duplicate NOAA parser. It refuses swapped IDs, wrong year/element, changed published values, nonblank quality flag, truncated row and false 269-width excerpt.
- New document roles **P1-71 / P1-72** distinguish NOAA Bar Harbor original *data* and NOAA first-party *metadata*. Directed edges **E111–E113** encode the shared-formatter/documentary relation, two-station comparator and absence of causal conclusion. Station metadata is not counted as an additional observing instrument.
- Existing [revisable source world](../receipts/PsychotronicsEllsworthRevisableSourceWorld20261026.json) now separates Bangor and Bar Harbor claims and a comparison claim, with conditional invalidation: withdrawing Bar Harbor source reopens only its dependent claims, while Bangor rainfall and Reich's narrated chronology remain independently classified. Root `noaa-ghcnd` remains **one custodial publisher/dataset family**, but two station IDs are distinct station observations.
- Tests are synthetic/adversarial source-content and arithmetic validations only, not a certificate of NOAA original remote bytes, historical gauge times, rainmaker effects or instrument reliability. CI/Agda are not evidence obligations in this source-first Phase 1.

## Remaining original-document Pareto frontier

1. **A2-site/time:** original Ellsworth-nearest 1953 daily/hourly meteorological pages and contemporaneous forecast or weather map; original observation-day closure at Bar Harbor and Bangor. More generic rain summaries add little.
2. **A1-person:** Gentry Smith's own words in original 2003 RVML recording (rather than RVML third-person publicity), dated Flanagan winding publication and claimed 1999 Croft handoff correspondence.
3. **B-original science:** 2013 vs 2024 Rodin coil identical rounded reported fields, raw measurement-session/coil original if published; separately Saikia 2019 original comparator not abstract-only.
4. **Stop rule:** no source-specific same-object original means record **unpaid**, rather than treating title association, publication count, or temperature/precipitation co-occurrence as corroborated extraordinary mechanism.

**Proof/status boundary:** original NOAA official row browser-inspected, record transcribed; complete native file uncaptured; decoder/replay source-written; no uploaded independent raw Ellsworth gauge, no Agda kernel claim, no authentic new physical intervention, no causal weather inference.
