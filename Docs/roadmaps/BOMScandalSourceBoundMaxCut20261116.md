# BOM 2026 data integrity and influence-claim investigation — maximum cut

**Updated 16 November 2026.** Australian case comparison, NOT the worldwide climate-denial population estimator. Johl Brown directs the research; OpenAI ChatGPT assisted with source review and proof/interface writing. Original observers, auditors, journalists, institutions and publishers retain authorship. No ESD surfaces are edited.

## Original sources and competing scopes

1. Bureau of Meteorology, *The science and truth of Australia's long-term temperature record*, issued 22 Oct, updated 26 Oct 2026: reports four duplicated post-1910 months relevant to ACORN-SAT, fewer than 200 affected values out of >7 million; correction completed 19 Oct; negligible national trend impact **according to BOM**, not independently recomputed. https://www.bom.gov.au/news-and-media/the-science-and-truth-of-australias-long-term-temperature-record
2. Patrick Lloyd, *Australia's Duplicated Temperature and Rainfall Data: What the Bureau Missed*, 1 Nov 2026: **author-reported, not independently reproduced here:** 44 temperature-copy stretches / 978 days / 15 stations, 571 historical temperature values removed between May and Oct at Sydney Observatory (515) and Charleville (56), and 1,337 rain-copy stretches / 61,877 days / 1,191 stations. Lloyd explicitly interprets them as apparent data-handling errors, not evidence of an agenda. https://wattsupwiththat.com/2026/11/01/australias-duplicated-temperature-and-rainfall-data-what-the-bureau-missed/
3. Ben Fordham / 2GB, *'Dodgy data' – Weather Bureau accused of climate conspiracy*, 18–19 Oct 2026: documented publisher framing; not an original-data audit, independently measured audience effect or proof of intent. https://www.2gb.com/dodgy-data-weather-bureau-accused-of-climate-conspiracy/

**Scope firewall:** ACORN-SAT's 112 selected locations, raw-temperature station network, and rainfall station network are three different denominators. Do not conflate number of rain days with number of temperature values, or error counts with national trend effect, or anomaly with deliberateness. Verify BOM's statement and Lloyd's audit symmetrically.

## Exact engineering, empirical and causal gates

| Gate | Target result | Current status | Acceptance |
| --- | --- | --- | --- |
| B0 | Immutable original before/after CDO source snapshots | **OPEN** | May and 29–30 Oct original bytes and capture receipts, SHA256, source identity; a current mutable URL is not the historic archive |
| B1 | Repeat/copy detector with severe controls | **OPEN** | predeclared thresholds, same station/variable/precision regime, seasonal/rounding/zero-rain baselines, neighbour comparisons, negative-control false discoveries |
| B2 | Paper-original verification | **OPEN** | original handwritten same-station/date/variable record and independent examiner; station renumbering/duplicate instruments separated |
| B3 | Same-object version/change ledger | **CODE + SYNTHETIC TESTS; REAL DATA OPEN** | SHA-bound manifest, precise station/date/variable join, missing *row* vs missing *value*, flag and formatting-only controls |
| B4 | Local/national quantitative sensitivity | **OPEN** | actual monthly/annual data, homogenisation and weighting, ACORN-SAT release version, rainfall local effects and uncertainty |
| B5 | Original media-transmission graph | **PARTIAL** | original Berger/Sherrington report, Graham Lloyd original article, Fordham original audio/transcript, matched exact claim versions and dated syndications |
| B6 | Documented funding and editorial rights | **PARTIAL** | actual signed commission/payment/right/communication, not ownership, proximity, political benefit or repeated wording alone |
| B7 | Exposure and measured cognitive effect | **OPEN** | independent exposure and before/after response measures, matched controls and uncertainty |
| B8 | CCDCOE six-gate same-operation admission | **OPEN** | original intervention, exposure, validated mechanism, causal discrimination, independently sourced intent/targeting, original actor attribution all for SAME case |
| B9 | Agda / TOE acceptance | **TOE EXPORT SOURCE-WRITTEN; KERNEL OPEN** | current Agda kernel and preflight run; PR #1251's 13 aliases forward-ported without replacing newer master imports; regression receipt |

## Highest-alpha implementation this round

- `DASHI/Governance/BOMVersionedSameObjectCorrectionExact.agda`: two snapshot-indexed rows must share exactly one typed station/date/variable key to inhabit `SameObjectChange`. Distinct `PaperComparison` requires a further original-archive match. Reuses `DASHI.Core.IntersectionalNonFactorability` to show an error flag cannot alone determine downstream climate trend. Its finite witness is NOT a climate measurement.
- `scripts/bom_versioned_same_object_audit.py`: pure-stdlib manifest/CSV comparison checks source SHA256, canonical dates, variable scope, duplicate keys and path traversal, and distinguishes row/value removals, numeric formatting changes and quality-flag edits. The output unconditionally labels the *unpaid* source-authentication, paper-review, trend and intent gates false.
- `tests/test_bom_versioned_same_object_audit.py`: eight synthetic unit tests independently executed locally 16 Nov 2026, all passing. Python syntax compiled. **No Agda compiler was available and no kernel certification is claimed.** No real May/Oct BOM source data were fed into this code.

The two current master aggregates, \`DASHI/Unifier.agda\` and \`DASHI/EverythingTOESymmetryResolved369.agda\`, now have additive direct aliases for the non-promotion proof, preserving their preceding content. Their kernels have **not** been checked. PR #1251's separate 13 original governance aliases still need conflict-aware reconciliation.\n\n## Next exact empirical cut, in order

1. Acquire *immutable* original May and late-Oct CDO snapshots and timestamps, not guessed reconstruction from summary counts; check released quality flags.
2. Run B3 ledger on exact station/date/variable and independently audit Sydney 515 and Charleville 56 alleged removals. Compare original paper archive. Deleted *public digital* values are not necessarily deleted *original* observations.
3. Build B1 streak detector (date shifts, paired tmax+tmin, wet-day rainfall, sensor precision, permutation controls). Audit 44/978 and 1,337/61,877 candidates, and the 1910 seven-day Sydney overlap, with unresolved category and blinded independent reviewers.
4. Run B4 downstream calculations against actual ACORN-SAT dataset versions, weighting/homogenisation model and original station data; report distribution of impacts and uncertainties.
5. Obtain original Berger/Sherrington audit, Graham Lloyd exact article and Fordham audio; construct time-indexed claim-language lineage, original author vs syndicated narrator, editorial directions vs ownership only.
6. Reconcile #1251 with master TOE/Unifier without dropping any new imports; run pinned Agda and dashi-agda-preflight before claiming a checked formal theorem.
7. Seek independent audience data and explicit same-operation causal evidence only if obtainable; otherwise keep B7/B8 OPEN.

**Stop rule:** no new media/person adjacency without a new original claim, exact-source version, contract/payment, documentary instruction, audience response or measured causal consequence. These Australian records are a local stress test, not a worldwide source-concentration estimate. No original empirical gates were closed by code/schema-only work.

## 16 Nov — B1 / B4 / B5 source-bound maximum cut

### New executable owners and receipts

- `scripts/bom_streak_negative_controls.py` and `tests/test_bom_streak_negative_controls.py`: anchored, bounded exact candidate search within a station across dates and between stations on the same dates. Excludes long all-zero rainfall runs, enforces wet-day support, preserves missing-day gaps, recognises numeric-format equivalence, and reports deterministic month-rotation controls. **Nine synthetic tests passed locally.** It cannot yet reproduce Lloyd's 381/402 intermittent matches or statistical false-discovery rate and cannot validate geographic independence; high-multiplicity anchors are reported skipped, so a no-result cannot mean an exhaustive no-anomaly certificate. This is B1 **partial code**, not a whole-network replication.
- `scripts/bom_panel_trend_sensitivity.py` and its tests: exact rational identity for weighted least-squares differences on *the same derived annual panel*. Requires identical nonmissing years and fixed positive weights. Reports full signed difference and triangle bound; no unreported imputation or altered denominator. **Eight synthetic tests passed locally.** No real paired before/after homogenised annual panels; B4 empirical outcome **OPEN**.
- `Docs/support/reference/bom_abc_mediawatch_station_excerpts_20261026.json` and `tests/test_bom_abc_source_excerpts.py`: three exact source-typed samples transcribed from Berger's supporting tables hosted by ABC Media Watch on 26 October, not independent CDO archive bytes. **Four locally run tests passed**: Sydney 066062 1910 January 25–31 = February 1–7 (seven numeric matches, below the detector's preregistered 12-day default); June 1943 = June 1944 (30/30); December 1935/1936 shows first 14 matches, 2 missing 1935 days corresponding to populated 1936 days, then 15 matching numeric values including the shared junction on day 17 (accumulation metadata differs). No original paper record authenticated, no copy direction inferred, no trend impact measured.

### New primary-source provenance correction

ABC Media Watch (26 October 2026) publishes **both** original party responses and five attachments attributed to Berger: https://www.abc.net.au/mediawatch/episodes/bom/107310398 . The 26 Oct BOM spokeswoman reply at https://live-production.wcms.abc-cdn.net.au/109ad311a673359cf5652021d85173b8 explicitly:

- **acknowledges** 1943/44 June and 1935/36 December examples and says each is **already included** in its small original duplication count, with affected copies showing no data while original logbooks are consulted. Do **not** cite these as *new* counterexamples to the Bureau's 'no further months beyond the audited cases' statement;
- **investigates**, but does not yet confirm, the Jan/Feb 1910 seven-day match. It says the week was included in the stated upper count while being checked. This is not equivalent to a confirmed copy cause or a final correction;
- distinguishes temporary no-data exclusion from the planned later logbook restoration. A 19 October v2.7 update does not by itself certify that every original historical value was reconstructed.

Berger's statement is available at https://live-production.wcms.abc-cdn.net.au/8b73f188d35eefe9c037efc6982be7f7 . The publisher's 25 Oct reply is at https://live-production.wcms.abc-cdn.net.au/f1706e61b630c6095fe4d5931a140c29 . These are source-attributed positions, not independent confirmation of the 39-page report's claimed Monte Carlo probabilities or 'human fingerprints'. The complete 39-page audit is not authenticated/ingested, though Berger states in his reply that he sent it via Andrew Wilkie before publication.

The BOM ACORN-SAT original site catalogue states **Charleville Post Office 044022 supplied 1910–48**, with Aero 044021 taking observations from 1942: https://www.bom.gov.au/climate/data/acorn-sat/documents/ACORN-SAT_Report_No_5_WEB.pdf (printed page 27). The 1914 August/September candidate must be checked against Post Office 044022, not inferred from Aero 044021; overlapping site periods, later moves and composite series require a dated physical station lineage witness.

### Unpaid gates after this cut

B0 May and 29–30 Oct raw CDO archive SHA256/capture receipts; B1 complete network + gapped-match + robust controls and original paper directions; B2 archival pages with independent review; B3 actual paired raw revision events (571 historical removals alleged, not reproduced); B4 actual station and national series sensitivity with homogenisation or published adjustment code; B5 unmodified complete 39-page Berger/Sherrington report, original 2GB recording, other dated media and exact reprint joins; B6 real documentary commissioning/editorial rights; B7 audience exposures and causal study; B8 single-operation six-stage admission; B9 Agda kernel and #1251's separate 13 exports forward-port.

**Acquisition order:** (1) secure original BOM CDO May/Oct byte snapshots or request immutable copies and change log from the Bureau and Patrick Lloyd, (2) original Sydney/Charleville logbooks and metadata, (3) complete Berger/Sherrington audit with actual dataset/method/seed/code, (4) ACORN-SAT 2.6/2.7 release code/panels and separate isolated-raw-correction variant, (5) original media audio and signed finance/editorial sources. Do not rerun pseudo-empirical tests on summaries alone.
