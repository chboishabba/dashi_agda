> **27 October corrigendum — source-format correction:** The first version of the original ISD parser misread the first-four-character **variable-length** count as the whole record length; its previously claimed 5 passing synthetic fixtures were self-consistent but **did not validate NOAA's actual layout**. The current committed parser uses the original NOAA `105 + variable` rule and was exact-Git-hash matched and **11/11 adversarial regression tests executed successfully** on synthetic fixtures. The original Bangor 1953 gzip bytes are still unacquired. NOAA also announced 2026 migration of old ISD data distribution to S3. See [original primary-format and cloud-access corrigendum](psychotronics-20261027-isd-original-format-migration-corrigendum.md) before relying on any earlier reader acceptance claim. No original 1953 actual rainfall hour was obtained.

# 27 October 2026 — 1953 Bangor first-party original hourly/synoptic archive object located

**Canonical owner:** [DASHI psychotronics PR #1242](https://github.com/chboishabba/dashi_agda/pull/1242), extending existing source attribution, NOAA 269-column original GHCND July 1953 station rows, two-gauge spatial audit, July 1953 conditional bucket counterexample and revisable claim world. Original agency/source: **NOAA/NCEI Integrated Surface Database (ISD)** and historic meteorological observers; historical device claims credited to Wilhelm Reich (1954); this precise acquisition/provenance bridge by **Johl Brown with OpenAI ChatGPT assistance**. This is NOT new meteorological observation or an original experiment.

## A1 original-source breakthrough: actual indexed 1953 station-year file

**Direct [NOAA/NCEI first-party 1953 original ISD directory](https://www.ncei.noaa.gov/pub/data/noaa/1953/)**, checked 27 October 2026, explicitly lists:

- **`726071-14606-1953.gz`** at [its original NCEI archive URL](https://www.ncei.noaa.gov/pub/data/noaa/1953/726071-14606-1953.gz)
- **160,944 compressed bytes** listed, server file modification 31 August 2018, 23:35
- **`726071`** is the historic ISD USAF station prefix actually listed in this 1953 year (NOT presumed to be `726070`, a modern/alternate identifier); `14606` is the matching five-digit WBAN station family also underlying Bangor GHCND `USW00014606`
- **NOT checked:** full original gzip bytes, original file hash, records on 6–7 July 1953, their UTC observations, precipitation observations, quality codes, local Maine time/daylight-saving conventions, and whether individual GHCND daily and ISD hourly records derive from overlapping reports

Source directly supports **the existence and exact identity of the historical station-year file**, not *date/hour coverage*. It is a stronger payment than the general GHCN `OBS-TIME` field readme because it identifies a concrete original station-year hourly **object** rather than a potential column. The [NOAA original ISD overview](https://www.ncei.noaa.gov/products/land-based-station/integrated-surface-database) describes the database as integrated hourly/synoptic observations with weather, wind, pressure, and possible precipitation, including historic paper-entered material. The NOAA index reveals no individual `AA1` original payload until decompressed; never claim an hour of rain from the filename.

**Retrieval limitation:** direct browser opening the gzip gives unsupported application/gzip; direct container download also failed. This does NOT invalidate the publicly listed source object. Do not fill in actual dates or weather by extrapolating from NOAA's daily (6.6,19.3,4.6) mm record or the Bar Harbor 3 NW daily record.

## Exact original-format fail-closed consumer

New [Bangor 1953 ISD UTC observation inventory checker](../../scripts/check_psychotronics_bangor_1953_isd_original.py) is a deliberately limited *consumer*, not a competing parser/ontology:

- Source object filename exactly `726071-14606-1953.gz`; checks header declared record length, USAF/WBAN, date and UTC HHMM control stamps, rejecting invalid/duplicate identification at source-record level.
- When supplied the authentic local original-format gzip, counts observations and lists UTC timestamp labels across **5–9 July 1953** with no conversion to an unverified July 6 Ellsworth 22:00 local time.
- Labels observed record UTC timestamps only; it **does not decode liquid-precipitation `AA1–AA4`**, present-weather `MW` fields or station pressure. Thus even a positive row count is not a claim of precipitation at that hour.
- Hashes a *locally supplied* file and truthfully flags it as **not automatically authenticated NOAA publisher bytes**. Successful parsing never claims full remote source custody.
- No user-facing claim of hourly 1953 data content unless the actual gzip is supplied and decoded. No inference of new energetic, quantum, meteorological-control, clinical or psychic physics.

**Exact execution proof here:** the *same exact Python Git blob*, verified by local `git hash-object` and connector GitHub `fetch_file` as **`5a16819ea6d37ee4f9a331ecc6029c1b3ab0e6c7`**, executed locally on synthetic fixed-width and gzip fixtures: 5 intentional malformed-source negatives correctly rejected, synthetic gzip source scan passed, source content marked `publisher_1953_original_bytes_acquired=false`. Python `py_compile` also passed. **These are genuine executed tests of exact committed source**, not exact NOAA archive observations. Agda kernel and CI not run.

Exact command from repository root:

`python3 scripts/check_psychotronics_bangor_1953_isd_original.py --self-test`

After the real original gzip is downloaded:

`python3 scripts/check_psychotronics_bangor_1953_isd_original.py --original-isd /path/726071-14606-1953.gz`

This code is intentionally bounded; decoding `AA1–AA4` needs a separate checked source-native ISD format/quality receipt before claiming precipitation times.

## Ibrahim/snowball source graph and latest PR cross-pollination

- New **P1-79** original archive object with first-party NOAA custody, distinct from P1-63 original Bangor GHCND daily gauge series and P1-73 original NOAA OBS-TIME *schema*. **E123/E124** restrict same-station-family and temporal source relationships; they do not equate hourly and daily data or count two independent experiments.
- Case-specific 1953 source world adds an **`noaa-isd-hourly` source-root** for original dataset provenance, *tagged potentially co-origin with NOAA GHCN and same historical observers*. New archive-existence state remains separate from **unpaid date-specific hourly data** and **unpaid causal reconstruction**; changing publisher archive identity selectively reopens its source-dependent claims.
- Existing typed Agda `PsychotronicsSuccorSourceAtlasExact` gets **one** original NOAA source instance and bounded claim with *existing* NOAA original custodial attribution root, while `PsychotronicsSuccorAttributionRegression` count and no-promotion guards are updated. Distinct **dataset roots in a JSON source-world ledger** need not be independent human observers, publishers or physical instruments.
- Cross-pollinate only reasoning: [#1268 source-root deduplication](https://github.com/chboishabba/dashi_agda/pull/1268), [#1266 observational collision](https://github.com/chboishabba/dashi_agda/pull/1266), [#1251 evidence genealogy and repeated-claims nonpromotion](https://github.com/chboishabba/dashi_agda/pull/1251), [#1245 revisability](https://github.com/chboishabba/dashi_agda/pull/1245), and existing stacked [#1252](https://github.com/chboishabba/dashi_agda/pull/1252) hypothetical experimental steelman. No unmerged sibling imports, no new generic ontology.

## Pareto / stop rule

**Highest next information payment:** download the exact original `726071-14606-1953.gz` from NOAA and preserve SHA-256/remote first-party custody; use the limited existing header reader to test if 6–7 July UTC hour labels actually occur, then independently interpret precip fields with the original ISD specification and quality flags; align UTC to documented Maine time rules for July 1953 and Bangor to Ellsworth geographic disparity. If missing actual dates or precipitation, record a **negative coverage result**, not a causal disproof.

**Parallel original:** actual 6–8 July 1953 Weather Bureau map page images and forecast time/legend; Gentry/Flanagan first-person technical diagram/account; original 2013/2024 Rodin raw measurement-session files/2019 full paper. Do not substitute social testimonies or secondary republishing for these original source objects.

The formal (24)-bin projection and synthetic counterfactual nonidentifiability demonstrated on this PR remain intact: neither an authentic hourly Bangor meteorological record nor a spatially associated 1953 rain event alone establishes what weather would have occurred without Reich's equipment.
