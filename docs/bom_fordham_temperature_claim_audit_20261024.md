# BOM historical-temperature duplication / Ben Fordham media framing — source-root audit

**Case date:** 24 October 2026 (Australia/Brisbane). **Status:** bounded source-and-claim formalisation; not a completed forensic replication or finding of motive/coordination.

**Formal owners:** `DASHI/Governance/BOMFordhamMediaClaimAuditExact.agda` and `BOMFordhamMediaClaimAuditValidation.agda`. Reuses existing `TypedGenealogyEdgeExact`, `EvidenceGradedGenealogyCore`, `ClimateGenealogyTypedCasesExact`, `HansonOneNationPoliticalEcologyExact`. Its Bannon/Bondi comparator currently exists on **open PR #1131**, `DASHI/Cognition/BannonPlaybookBondiMobilisationCrossPollinationExact.agda`. Do not import an unmerged branch file into master.

## Primary answer: the error mechanism

The Bureau of Meteorology's **22 October 2026** first-party statement (https://www.bom.gov.au/the-science-and-truth-of-australias-long-term-temperature-record) says:
- It checked the data inspected by the outside report and found **four duplicated months after 1910** relevant to its ACORN-SAT national temperature dataset, involving **fewer than 200 daily values in more than 7 million**.
- All four are from **handwritten pre-1946 observations subsequently manually digitised**.
- Historical digitisation used methods including **1960s punch-card systems**; the Bureau identifies these as a **possible** source of isolated transcription mistakes, but says it is **still checking whether that happened here**. This is a causal *candidate*, not a finding.
- Values were corrected in the update completed **19 October 2026**. The Bureau says the impact on Australia's long-term trend is **statistically negligible**, and rejects allegations of intentional manipulation. Both statements belong to the Bureau until an independent same-object reproduction is installed.
- The Bureau says it found no further duplicate months in its network beyond those cited by the outside report and confirmed. This does **not** settle every separately alleged pattern or quality concern without common input definitions and affected records.

Separate original and analysed data: BOM ACORN-SAT methods: https://www.bom.gov.au/climate/data/acorn-sat/. Historical **digitisation** is paper-to-database transcription. **Homogenisation** derives a separate climate trend series to handle station moves, instruments, surroundings, and other discontinuities; it does not mean mechanically editing archived paper values. The BOM says its original observational records remain accessible. An error in a digitised record is real even where aggregate trend effect is tiny.

### Object identity / boundary

| Object | Status | Exact limit |
| --- | --- | --- |
| August **1867/1907** Sydney Observatory duplication | Archival verification **reported** by Graham Lloyd and reproduced by Jo Nova | 1867 is pre-1910; *do not count* this example among BOM's four **post-1910** ACORN-SAT months. Archival ledger images and the exact digitised data version are not retained here. |
| Four duplicated post-1910 ACORN-SAT months | BOM **acknowledgement** | Four, <200 affected daily values, pre-1946 handwritten origins. Precise stations/dates and a machine-readable correction diff remain to acquire. |
| More than 500 structured repeats, 879 value traps, hundreds of anomalies and directional adjustment claims | **Berger/Sherrington allegations, secondhand at present** | Full original report, code and input snapshots not obtained; counts and calibration nulls must not be promoted as verified errors, nor collapsed to the four BOM cases. |
| 1960s punch-card explanation | **BOM candidate** | Specific historical ingest incident still unproven. |
| Statistical negligibility for national warming | **BOM analysis claim** | Obtain 2.6/2.7 corrected series and recompute with and without confirmed duplicates plus sensitivity bounds. |
| Deliberate data manipulation / climate conspiracy | **Unproven accusation** | The mistake does not establish agency or intent. |
| Fordham's complete spoken wording | **Not yet transcript-verified** | Publisher headline/description and podcast metadata are available, not a timed verbatim transcript. |

**Important conflicting secondary detail:** a later Marohasy Substack article inconsistently calls the copied August month 1909, whereas the contemporary Lloyd/Nova/CFACT and Clintel accounts consistently say 1907. Until the archival date and precise series are checked, preserve this as a conflict; do not silently normalise it. 
- https://www.cfact.org/2026/10/18/boms-scientific-scandal-the-raw-data-is-not-raw/
- https://clintel.org/australian-temperature-records-errors/
- https://jennifermarohasy.substack.com/p/historical-temperatures-how-erasing

## Source tree and timing

**S0 — reported primary-audit producer:** Tom Berger and Geoff Sherrington; precise original audit version, hash, appendices, datasets and code **unacquired**. Attribution for detection is maintained without pretending possession or computational verification.

**S1 — original archival comparison reported:** Graham Lloyd, *The Australian*, mid-October 2026, reported handwritten-versus-digital comparison at Sydney Observatory. Journalist's verification claim is distinct from own examination of the archival folio. Related commentary: Jo Nova/CFACT 18 October (above). *Do not double-count Nova, Climate Change Dispatch, EIKE or other syndicated Nova text as independent reproductions.*

**S2 — original programme publication:** Ben Fordham/2GB, **19 October AEST**: https://www.2gb.com/dodgy-data-weather-bureau-accused-of-climate-conspiracy/ . Apple Podcasts dates the 4-minute episode **18 October 2026, 21:55 UTC**, corresponding to **19 October, 07:55 AEST**: https://podcasts.apple.com/sg/podcast/dodgy-data-weather-bureau-accused-of-climate-conspiracy/id157670116?i=1000796975224 . Headline invokes 'climate conspiracy'; publisher body 'The BOM has done it again' and says an outside audit found copied readings. **No blanket judgement of every spoken claim is made without a transcript.**

**S3 — institutional response:** BOM 22 October 2026 (source above). **This response postdates the episode**; later objections can qualify the programme but cannot alone prove Fordham knew them on 19 October.

**S4 — correction dataset:** ACORN-SAT v2.7, updated October 2026 per BOM official methods. Raw files and version diff not acquired in this case. **A statement that a correction was completed is not itself independent verification of the delta.**

## Actor/institution relations: confirmed vs candidate

- Ben Fordham **hosts** 2GB breakfast, documented by 2GB programme and talent material. Direct public personnel association.
- Since **1 May 2026**, 2GB has been owned by the Laundy Family Office and operated as **Tapt Media** after the acquisition from Nine, per Tapt's *own announcement* https://taptmedia.com.au/tapt-media-launches-as-australias-premier-independent-audio-powerhouse/ and independent ABC reporting of the deal https://www.abc.net.au/news/2026-01-30/nine-radio-sold-to-arthur-laundy-talk-radio-shrinking-audience/106286352 . Arthur Laundy's son Craig is a former Liberal MP. Ownership, family political ties and editorial directions are different relations.
- **Kyle Sandilands:** documented breakfast-radio market rivalry with Fordham, not joint political operations: https://radioinfo.com.au/news/triple-m-goes-to-2gb-for-whats-happening-at-kiis/ . No Kyle-specific formal proof owner identified in this checked default-branch corpus; preserve as acquisition/repo-search gap, not assertion of absence everywhere.
- **Pauline Hanson:** substantial One Nation source ecology exists in `HansonOneNationPoliticalEcologyExact` and its validation, plus `HansonHerzogEmancipatoryGrammarCrossPollinationExact`. Fordham's **21 October** question to Senator Sarah Henderson referenced Pauline Hanson *Please Explain* cartoons: https://sarahhenderson.com.au/breakfast-with-ben-fordham-2gb-21-october-2026/ . Mention does not prove an affiliation, endorsement, or direct Hanson interview.
- **Bondi:** 2GB's 2025 Bondi Beach terror attack reporting, led in part by Fordham, was awarded a journalism prize: https://radioinfo.com.au/news/2gb-takes-home-kennedy-award-for-coverage-of-bondi-beach-terror-attack/ . The existing Bannon/Bondi work examines downstream framing and institutions; **no inflammatory Fordham quotation has yet been isolated**. Also keep **2024 Bondi Junction** and **2025 Bondi Beach** distinct.
- **TPUSA, Turning Point Australia/TPAU and Steve Bannon:** **no first-party/documented Fordham personnel, payment, instruction, co-production, or event participation edge was established in this investigation**. Record as unverified hypotheses, *not* negative proof of absence and *not* factual network edges. Similar rhetorical structure, right-wing platform positioning, elite social proximity, or an accusatory headline are insufficient.

### Additional source-defined Australian media and Bondi samples

- **2025-12-18:** Ben Fordham Live published a three-minute episode titled *'We're angry' - PM slammed over response to Bondi terror attack* (original publisher's syndicated podcast listing: https://music.amazon.co.uk/podcasts/2686e400-47fa-4f4f-94b3-b95934a496b2/episodes/b7dd042e-cf37-47eb-bfc6-b79cc0dcf598/ben-fordham-live-on-2gb-breakfast---highlights-%E2%80%98we%E2%80%99re-angry%E2%80%99---pm-slammed-over-response-to-bondi-terror-attack%E2%9D%97). This establishes **post-attack government-response criticism**, not anti-Muslim words or proof of a Bannon mobilisation channel.
- **Undated older 2GB archive:** The original Fordham programme's *Groups using government funding to spread Islamic radicalisation* hosts **Mark Latham** discussing a performance that criticised Hanson, alleging funded radicalisation: https://www.2gb.com/?p=75904 . Attribute the alleged radicalisation to **Latham**, the headline and broadcast to **2GB**, and the actual poetry performance separately. No independent finding about those allegations is supplied by this page.
- **2025-12-15:** AAP FactCheck, *Disinformation operation targets Bondi terrorist attack*: https://prod-ss.aap.com.au/factcheck/disinformation-operation-targets-bondi-terrorist-attack/ . AAP demonstrates **fabricated quotes attributed to Pauline Hanson** circulating from overseas-run Facebook pages. These were not Hanson's actual words and cannot be used as evidence of Hanson, Fordham or TPUSA involvement. This is a high-value negative-attribution regression.
- **TPAU source:** Turning Point Australia's own https://tpaust.com.au/about/ describes **Joel Jammal**, Farage speaking-tour organisation and independent-media activity. A first-party organisation page supports its self-described organisational history, not a Fordham connection. A separately published Josh Szeps interview https://podcasts.apple.com/au/podcast/turning-point-leader-vs-josh/id1002920114?i=1000754064574 documents Jammal's political role and discussion of the Hanson/One Nation right. The bridge to Fordham remains **unverified**.

## Disinformation vs evidence

The statement 'BOM duplicated historical records' is supported. A suggestive 'climate conspiracy' headline converts a **specific acknowledged quality-control problem** into a **possibility of systemic bad faith** without public demonstration of agency or intent. It is fair to assess this as an **unsupported/conspiracy-framed inference**. Labelling a particular speaker as *knowingly* disseminating disinformation requires evidence of knowledge, intent and the **actual spoken statement at the time**—not just its framing.

For parallel scientific content:
```text
paper original --transcription--> digitised station record
digitised station record --quality control / selection--> ACORN-SAT input
ACORN-SAT input --homogenisation--> climate trend series
```
Keep separate hash/version provenance for each object. The original paper and digitised raw archive are not interchangeable. Correction of four months, trend sensitivity and anomaly counts answer different questions.

## Max-cut acquisition and tests

| Priority | Required same-object receipt | Operational discriminator |
| --- | --- | --- |
| P0 | Original signed/dated Berger–Sherrington audit, code, station/date tables, raw data snapshot | Are the duplicated months the same rows as BOM's correction? Do the >500/879 pattern counts survive sensible tropical/noise/null controls? |
| P0 | ACORN-SAT v2.6/v2.7 data and four pre/post correction rows, release notes, archive folio | Recalculate change to Australian national mean and long-term slope. Distinguish numerical impact from the failure of earlier quality controls. |
| P0 | Four-minute Fordham audio, timestamped transcript and 2GB page version history | Quote exact spoken claims and timing. Distinguish describing allegations from personally endorsing intent/fraud; record any later correction. |
| P1 | Fordham Bondi Beach 2025 programme timestamps/transcripts | Identify particular rhetoric, speakers, guests and corrections; no transport of 2024 Bondi Junction claims. |
| P1 | Named TPUSA/TPAU/Bannon/Fordham joint sources, if any: appearance, contract, production credit, correspondence | Only direct evidence can move a *candidate network* to a typed personnel, funding, commissioned-content or direction edge. |
| P1 | Media framing control corpus: 2GB, other outlets, original Lloyd report, BOM response | Test whether conspiracy/fraud language is propagated beyond reporting actual numerical duplicates, accounting for timing and common syndication. |

### Owner integration

1. This case reuses `TypedGenealogyEdgeExact` to distinguish **personnel**, **organisational ownership**, **broadcast adjacency** and **historical transfer**. Only the first three have installed receipts; no Bannon/TPUSA transfer edge is asserted.
2. `ClimateGenealogyTypedCasesExact` already handles tobacco-to-climate **method recurrence vs demonstrated method transfer**. Reuse its noncollapse principle; don't merge this 2026 data-quality episode with the historical tobacco/API chain without a new original continuity document.
3. Hanson/One Nation existing work contributes media-ecology and nonfactorability, not a default Hanson↔Fordham association.
4. Open PR #1131's `BannonPlaybookBondiMobilisationCrossPollinationExact` can consume the case once integrated: `public rhetorical pattern ≠ coordination; event authenticity ≠ framing ≠ policy effect`. Neither endpoint should be modified to quietly infer a hidden organising actor.
5. SensibLaw / ITIR can ingest each source as a separate `SourceUnit`, with `Claim` ownership, dated `EvidenceReceipt`, content hashes and explicit unresolved hypothesis objects. No new evidence ontology necessary.

**Proof status:** two Agda modules provide source-attributed case *representations* and finite negative-promotion witnesses. They **do not prove the external-world facts**. No Agda kernel checking or ACORN statistical recomputation is claimed by this tranche.

## Follow-up max-cut: scale of error and documented second/third-order influence — 24 October 2026

### Numerically bounded toy scenarios (not reconstructed BOM outputs)

BOM says **fewer than 200** historical daily temperature values out of **more than seven million** ACORN observations. Use generous upper ratio `200/7_000_000 = 1/35_000 = 0.002857142857% of entries` for equal-weight arithmetic only. If an affected observation's absolute error is no more than `D` Celsius, then

`|Delta(unweighted_mean)| <= (200/7_000_000)*D`.

For `D = 2, 10, 50 C`: the *full-record equally weighted mean* changes by at most `0.00005714, 0.00028571, 0.00142857 C`, respectively. The 50 C case is purposefully extravagant (wrong observation entries are duplicates of a **same calendar month**, not selecting record hottest days).

For another extreme: if **all** 200 errors land at maximum chronological leverage in a uniformly sampled **116-year** *raw-observation OLS* regression, the approximate worst-case slope disturbance is `(600*k*D)/(N*116)` C per century; with `D=10 C`, **0.001478 C/century**. This is an illustrative model, not the actual BOM/ACORN-SAT spatially weighted anomaly trend. It may be *invalid* for gridded series weights, nonuniform temporal coverage, infill and homogenisation; no universal trend bound is asserted from counts alone.

Station-month matters: if a duplicate month differs by **2 C in its monthly mean**, it can change the source station's **one monthly mean by 2 C**. Across a hypothetical equal-weight 112-station national mean and 12 months, its contribution to the **one year's** national average would be `2/(112*12) = 0.001488 C`; four such distinct months in the same year would be 0.00595 C. In real ACORN, retain area weights and their dates. Thus **local monthly effect** and **continental century trend** are distinct outcome objects; a detectable mistake is not automatically a warming-trend problem.

August **1867 vs 1907** at Sydney Observatory compares the **same season**, not summer readings falsely replacing winter. Marohasy's 19 Oct article cites original August 1867 paper minimum **3.9 C on the 3rd** and digitised month's copied August 1907 minimum **5.6 C on the 18th**. These are the **minima of different days/months**, not an aligned day-by-day residual or mean comparison. The evidence at https://jennifermarohasy.com/2026/10/australias-historical-temperatures-update-following-tom-berger-forensic-audit/ is a **participant commentary recounting an archival check**; exact original folios and means remain uncomputed. Pre-1910 1867 is NOT an ACORN national-trend data point. Beware that a subsequent Marohasy Substack version says 1909 despite her previous 1907 account; preserve version/date conflict.

Exact rational tests: `tests/test_bom_climate_sensitivity_bounds.py`. They prove only assumptions about an *illustrative model*, not BOM's statistically negligible claim. The 200-row chase should be **low priority** if the user cares about the scale rather than archival provenance.

### Ownership: two genuinely separate radio firms, plus one surviving revenue right

1. **2GB** belongs to **Tapt Media / Arthur Laundy's family** since 1 May 2026. Craig Laundy is Arthur's son and a former **Liberal** MP. This supports a documented **family/party-history relationship**, not orders to Ben Fordham. Tapt's first party corporate notice: https://taptmedia.com.au/tapt-media-launches-as-australias-premier-independent-audio-powerhouse/ and ABC January 2026 https://www.abc.net.au/news/2026-01-30/nine-radio-sold-to-arthur-laundy-talk-radio-shrinking-audience/106286352 .
2. **KIIS 106.5** was/is owned by **ARN Media Ltd**, publicly traded. The Kyle/Jackie O program and the two $100m presenter contracts terminated in March 2026. ANN 2025 annual report: https://investors.arn.com.au/announcements/gao5Z3-annual-report-2025 and March 2026 announcement https://arn.com.au/market-annoucement-the-kyle-jackie-o-show/ .
3. Kyle's new subscription-based **Kyle Sandilands Live**, launched 10 August 2026 under his manager **Bruno Bouchet / King Kyle**: ARN retains a **19.9% revenue entitlement for three years in return for $1.5m advertising** as part of the June contract settlement, per ABC: https://www.abc.net.au/news/2026-08-10/kyle-sandilands-live-chris-minns-first-episode-start/107015998 . This is a financial/commercial distribution relation, **not proven shareholder voting rights or editorial control**. Correct the previous simplistic implication that Kyle is now wholly unaffiliated with ARN.
4. **News Corp and KIIS caution:** aggregator shareholder pages carrying **13.97% News Corp ARN** can be *stale*. ACMA's regulator snapshot explicitly says News Corp **ceased being a substantial holder in December 2025**: https://www.acma.gov.au/updates-media-interests-snapshot . Do not paint ARN as presently 14% Murdoch-controlled from that obsolete register. Southern Cross Media Group acquired Seven West and held ~14.54% ARN per ACMA February 2026; complex cross-holdings and large nominees are not editorial instructions.

### Higher-grade cross-source political network receipts

- **Kyle → Hanson messaging**, first-person quote: ABC 19 June, preserving speaker's “working on getting their messaging across” and the response from One Nation chief of staff James Ashby disputing any formal/informal **employment**: https://www.abc.net.au/news/2026-06-19/kyle-sandilands-new-show-after-arn-radio-contract-settlement/106815596 . Distinguish brief self-reported messaging help from retained paid advisory, contract, delivery, continuing campaign role or campaign effects.
- On 30 September, **Mediaweek** reports Kyle's subscription show hosted interviews with **Hanson and Barnaby Joyce**, and records an One Nation spokesperson confirming some time spent together: https://www.mediaweek.com.au/kyle-sandilands-bots-targeting-streaming-show . Kyle alleged bot attacks, but Mediaweek explicitly did **not** verify who was behind them. Do not convert allegations to foreign/government sabotage.
- **Rinehart → Hanson policy**: Hanson's 11 June interview says a pensioner employment policy was Rinehart's idea: https://www.abc.net.au/news/2026-06-11/one-nation-pauline-hanson-gina-rinehart/106787540 .
- **Rinehart-associated → One Nation material support:** her company donated an aircraft; Hancock Energy executive **Ian Plimer** and Hancock Agriculture executive **Adam Giles** each provided **$500k** individually according to ABC https://www.abc.net.au/news/2026-04-29/gina-rinehart-gifts-plane-to-pauline-hanson-one-nation/106620808 . Their money must not be attributed to Rinehart without payment documentation. The ABC's September 28 **Four Corners** adds Rinehart alleged attempts to recruit Liberal MP Henry Pike, contested and separately typed: https://www.abc.net.au/news/2026-09-28/gina-rinehart-allegedly-tried-recruit-liberal-mp-to-one-nation/107193248 .
- **Ian Plimer climate linkage:** he has made false or misleading climate claims, including the medieval-global-cooling assertion independently checked by Reuters https://www.reuters.com/fact-check/global-temperature-has-risen-not-fallen-since-medieval-period-2024-07-25/ . His professional and donation relationships are not evidence he briefed Fordham on the BOM story.
- **Hancock Prospecting → Advance**: AEC 2024–25 disclosures reported by SBS and ABC: **$895k**, https://www.sbs.com.au/news/article/political-donations-2025-federal-election-leadup/pi0lbzm5h . The regulator-identified donor, the recipient institution and date must remain explicit.
- **Advance → Bannon War Room associate → Liberal speaker event**: ABC's 23 February reporting from leaked conference audio establishes Bannon *War Room* international editor **Benjamin Harnwell** presenting at Advance's Sydney event with Tony Abbott, Liberal senators Price and Antic and other speakers: https://www.abc.net.au/news/2026-02-23/advance-lobby-group-conference-centre-right-mass-immigration/106371720 . It records his comparison of Merkel's migration legacy to the Nazis and Advance's disavowal of that statement. Coattendance is not attendee endorsement, nor proof Bannon funded the event.
- **Bannon–Palmer 2019 (canonical owner: PR #1131, BannonFaragePalmerAutomatedInfluenceReceiptsExact.agda, EFTA01615861)**: DOJ-released Epstein-associated texts attribute to Bannon a first-person statement claiming authorship of Palmer's $60m China/climate attack ads. Palmer's spokesperson denied this: https://www.theguardian.com/us-news/2026/feb/02/clive-palmer-denies-steve-bannons-claim-he-was-behind-billionaires-controversial-2019-australian-election-ad-strategy . Strong evidence that this **allegation was made**, not independent proof the claimed 2019 coordination occurred; see open PR #1131's prior `BannonFaragePalmerAutomatedInfluenceReceiptsExact` to avoid duplicate historical ownership.

### Regulatory findings about Kyle must not be blended with political allegations

- **ACMA 28 March 2023** found Paralympics programme decency breaches and a separate breach involving a threat to a journalist: https://www.acma.gov.au/articles/2023-03/kiis-1065-paralympics-comments-breach-decency-standards .
- **ACMA 10 August 2023** found mpox/gay-men stereotyped comments breached broadcast decency standards: https://www.acma.gov.au/articles/2023-08/kiis-1065-mpox-comments-breach-decency-standards .
- Distinguish **regulatory findings** from broader programme criticism, contemporary allegations in the Jackie O contract dispute, and *new political messaging*. Neither regulator decision establishes climate or Bondi misstatements by Kyle.

### Second-/third-order effects: strongest steelman & decisive discriminators

**Verified direct links** form an adjacency network but not a chain of commands:
```
Hancock / Rinehart --2024/25 funding--> Advance
Advance --2026 event podium--> Harnwell --War Room editor--> Bannon
                                  | co-event Liberal figures
Rinehart --aircraft/policy consultation--> Hanson / One Nation
Hancock exec Plimer --own $500k contribution--> One Nation
Kyle --self-reported message help; spokesman qualified--> Hanson
ARN --19.9% revenue share / $1.5m ad distribution--> Kyle Sandilands Live
Tapt / Laundy --station ownership--> 2GB --show--> Fordham --BOM headline
```

**Second-order candidate:** third-party donor support increases campaign resources, which may improve message reach; publishing negative institutional headlines may shape audience distrust beyond the numerical problem. **Third-order candidate:** learned distrust can affect future scientific-policy legitimacy, while donor/consultant networks can influence agenda selection and who is interviewed. These effects require an **outcome model**, not inference from adjacency.

**Potential empirical tests:** date-stamped advertiser/channel copy; repeated verbatim messaging strings across actual broadcasters/party outputs; speaker/guest booking contracts; pre/post listener polling; pre/post interview framing; regulator complaint outcome; corrected broadcast language and its reach. The closest available science case is a tiny direct data effect, potentially high second-order trust effect—not a numerical pretext for claiming fraudulent temperature trends.

### Priority adjustment

**P0 completed enough for rational scale choice:** exact worst-case toy bounds for 200/7m; no reason to spend dominant effort acquiring each row when broader goal is media influence. **P0 active:** Kyle's original Game Changers quote, One Nation spokesperson cross-quote, ARN revenue/advertising provision, ACMA rulings, Rinehart funding, Advance conference, Bannon-Palmer conflicting statements; all now have source locators. **P1:** direct Fordham source-channel/financing trace; exact four-min audio and identified climate assertions; Kyle coverage comparisons including Bondi and show guest transcripts. **P2:** station-specific daily correction diffs only if replicating the BOM's exact quantitative correction effect or if they affect a scientifically material breakpoint.


---

## 24 October follow-up: investor/ownership control surface and latest Friendlyjordies/ABC investigation

### Explicit canonical-owner correction

**No duplicate Bannon–Palmer evidentiary case.** The pre-existing, open PR [#1131](https://github.com/chboishabba/dashi_agda/pull/1131) already owns `DASHI/Cognition/BannonFaragePalmerAutomatedInfluenceReceiptsExact.agda#bannonPalmerReceipt`, including **US DOJ EFTA01615861**, a first-person Bannon claim, evidence of a Bannon–Palmer telephone conversation, Palmer's denial of tactical direction and independently reported Palmer campaign/SMS advertising deployment. This PR previously introduced a redundant `palmerBannonConflict` receipt; it has **been removed** and replaced with a read-only text pointer `bannonPalmerCanonicalOwner` and the exact EFTA identifier. This case does not import an **unmerged** branch module, nor does it overwrite its evidence grade. Merge/reference semantics can be resolved after #1131 lands.

### Corporate structure: what actually changed and who invested?

**Primary corporate registration:** Australian Business Register, `Kyle Sandilands Live Pty Ltd`, active from **29 June 2026**, **ABN 24 699 610 261**, **ACN 699 610 261**; sourced from the government register: https://abr.business.gov.au/ABN/View?id=24699610261 . The company's own https://kslive.com.au/terms says this is the operating entity. Neither shows a shareholder/member register or an ultimate beneficial-owner list.

**Public evidence for ownership:** In a direct RadioInfo first-person interview, Sandilands said multiple billionaires had made investment approaches but that his team would retain ownership until the venture's value was higher: https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/ . Guardian's 7 August 2026 media reporting characterised him as owning **100%** at that point: https://www.theguardian.com/media/2026/aug/07/alan-jones-trial-media-coverage-weekly-beast-ntwnfb . No completed external equity financing, current cap table or named outside shareholder was found in the checked public sources. `reported_interest != signed_investment != registered_equity != editorial_control`.

**Original ASX financial agreement, not equity:** ARN's announced June 2026 settlement is https://www.marketindex.com.au/asx/a1n/announcements/settlement-of-legal-proceedings-with-mr-sandilands-2A1677721 (original ASX release). It pays AUD 12.09m cash to Sandilands, supplies AUD 1.5m advertising over three years, and gives ARN **19.9% of NET revenue for UP TO three years**, subject to agreed thresholds and caps, with a noncompete against competing radio networks until March 2027. This does **NOT** mean ARN owns 19.9% of KSL shares; earlier shorthand `19.9% share of Kyle's venture` is too strong. ARN's interim report additionally describes the arrangement's ceiling relative to the settlement sum: https://financialfilings.com/filings/arn-media-limited/interim-quarterly-report/2026/57060553/ . Exact contract terms/threshold are not fully disclosed by the public announcement. The cash settlement creates resources for a start-up but is not an outside equity investor. KSL's subscriber receipts create a third financing channel, not proof of political sponsorship.

**King Kyle/production counterparties:** Sandilands' self-described King Kyle Group https://www.kingkyle.com/ and his manager/managing director Bruno Bouchet are operational infrastructure, not a second identified investor. AIIMS Creator Hub's first-party production credit for `At Home With Kyle`, https://aiims.group/aiims-creator-hub-kyle-sandilands-live/ is a vendor/producer relation, not named equity. Mediaweek's 22 September interview reports Joshua Fox's claimed AUD 1m subscription conversion from his launch trailer, **not independently audited**: https://www.mediaweek.com.au/joshua-fox-instagram-post-kyle-sandilands-1m . An outside agency's conversion anecdote cannot establish balance-sheet revenue.

**Proposed acquisition ≠ financed venture:** April news story https://www.news.com.au/entertainment/tv/radio/kyle-sandilands-plots-arn-takeover-but-still-needs-90-million-investor/news-story/ee29d7ba21ef87a7af1cbfb7987f07a5 discussed a speculative **AUD 10m Sandilands + AUD 90m outside-backer bid to acquire ARN**, and his contact with Stu Laundy. No identified committed backer, completed ARN takeover or stake in KSL followed from that report. Critically, the Laundy family's completed **2GB purchase** and the proposed **ARN takeover** are not the same transaction.

**Surviving Nine ↔ Tapt commercial relationship:** The 30 January Nine sale announcement explicitly anticipates collaboration using **9News reporters in radio, advertising sales, marketing, podcasts and Stan Sport/publican venues**, even after transferring equity in the 2GB/3AW/4BC/6PR network: https://newmedia.com.au/nine-announces-sale-of-radio-assets/ . This direct announced deal supplies an **institutional content/distribution relationship**, absent from a simplistic detached-owner chart. It does not show Nine directed Fordham's later BOM editorial claims.

### Which Friendlyjordies expose?

Jordan Shanks' original **22 October 2026** YouTube publication is titled **`breaking my silence`**, 39:13, https://www.youtube.com/watch?v=0Mo_tYIMMnU . The title/date/duration were independently cross-located via dated metadata https://zolotube.com/watch?v=0Mo_tYIMMnU and the **23 October Joshua Barnett / Michael West Media** report https://michaelwest.com.au/take-it-to-the-police-how-abc-brushed-off-friendlyjordies-warnings-about-reporter/ . This is the creator's own source for **what Shanks alleges**, not automatic independent confirmation of its whole narration; no complete timed transcript has been ingested.

#### Noncollapsed incident and provenance chain

| Date | What we can assert | Authority/evidence limit |
|---|---|---|
| November **2022** | Shanks' Bondi residence was firebombed; a man was later convicted for offences involving the arson and unrelated violence | The **2022 Shanks home** is NOT the **April 2024 Bondi Junction** attack or **December 2025 Bondi Beach** attack. Convicting a participant does not prove who commissioned the attack. No evidence links ABC's Fazal to planning the arson. |
| January–May **2024** | Kristo Langker, according to his account and later published reporting, warned of menacing statements attributed to Fazal. ABC publicly defended its reporter and directed the complainant toward police. | Contemporary media/participant accounts support the **existence of complaints and responses**, not that the alleged threatening conduct occurred. Fazal denies conveying threats. Internal ABC escalations require first-party case records. |
| September–October **2025** | Fazal appeared on a third-party crime podcast; alleged digital messages later circulated. | Newsroom published purported screenshots. Lamestream's contemporaneous technical examination says some sensational screenshots show discrepancies suggesting possible manipulation. No authenticated digital originals in this research corpus: https://www.lamestream.com.au/exclusive-these-messages-could-destroy-a-prominent-abc-journalist-but-are-they-real/ . |
| **28 May 2026** | ABC director Hugh Marks told Senate Estimates Fazal's employment terminated following its investigation concerning external podcast work. | Employment decision is explicitly a **different administrative reason** than its later withdrawal of programmes. No inference that allegations about Langker or arson were upheld in the employment inquiry. |
| **24 July / 17 August 2026** | ABC withdrew investigative episodes because of anonymous-source verification concerns and removed/edited further material. | Original institutional statements: https://www.abc.net.au/about/media-centre/statements-and-responses/four-corners-statement/106953658 ; https://www.abc.net.au/about/media-centre/statements-and-responses/abc-statement/107045888 . Different broadcast objects must not be counted twice. |
| **22 September 2026** | ABC Ombudsman identified breaches in **Cocaine Nation** and **Meth Highway**; ABC says aspects were **materially misleading**, formally accepted **seven recommendations**, corrected/withdrawn content. | First-party institutional response https://www.abc.net.au/about/media-centre/statements-and-responses/abc-response-to-ombudsman-review-of-cocaine-nation/107182808 . This establishes specific **editorial-source failures**, not the truth of unadjudicated threats. |
| **22–23 October 2026** | Shanks published `breaking my silence`; Joshua Barnett published a distinct reported synthesis and new chronology. | Creator's account and MWM reporting are different publication roots; MWM also draws on 2024 SMH, The Monthly, Media Watch, Lamestream and ABC. Do not multiply a shared anecdote into multiple independent witnesses. |

### Operational second-/third-order institutional testing

The correct ABC test is **not** `Ombudsman editorial breach => Fazal endangered Shanks`. It is:

```
source concern / complaint
 -> management received specific information [receipt]
 -> review or refusal of inquiry [decision object]
 -> reporter-public-defence / guest verification [institutional action]
 -> published content [separate data object]
 -> independent review / audit [standard-specific finding]
 -> correction and amended training or policy [implemented receipt]
```

**Second-order candidate:** failing to interrogate anonymous sources and dismissing relevant source-verification concerns may impair journalistic accuracy and source safety, leading to damaging institutional mistrust. ABC's public response and later Ombudsman findings ground a portion of this pathway, but **causation of threats/arson is absent**.

**Third-order candidate:** institutional credibility depends on published correction practices and whether third-party reporters, victims and whistleblowers can obtain prompt, independently reviewable responses. Compare public broadcaster correction design with advertiser-funded talk radio and subscriber-funded provocative content; avoid an easy false equivalence that all three institutions have the same legal editorial duties.

**Highest-value distinct acquisition roots (Pareto):** Original 2024 ABC exchange/case-handling instructions and contemporaneous Langker complaints (no speculation about private materials), 22 October video timed transcript (source segmentation/attribution), September 2026 Ombudsman executive summary and implemented corrections (not merely recommendations). **The Ombudsman's public finding is already an exact first-party anchor: no need for more generic commentary before building the case.**

### Existing-repo ownership and changes

- `DASHI/Governance/FriendlyjordiesNarrativeGovernanceTransportExact.agda` and `DASHI/Core/FriendlyjordiesGovernanceQuestionExact.agda` are pre-existing governance owners. `DASHI/Cognition/PNF/SensibLawFriendlyjordiesCompetingNarrativeExact.agda` and `SensibLawFriendlyjordiesSourceTotalityExact.agda` already carry the source-versus-counter account, provenance and no-orphan proof discipline. **This new ABC case does not replace these**.
- `DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Exact.agda` adds the OCT-2026 bounded ABC investigation; it imports the pre-existing FJ owner and references the 2026 source roots.
- `DASHI/Governance/FriendlyjordiesABCFazalSourceAudit2026Validation.agda` asserts no automatic `editorial breach => threat`, `screenshots => authenticated`, or `conviction => mastermind` promotions. The evidence labels are instantiated source claims, not a kernel-verified proof of factual external-world event occurrence.
- `DASHI/Governance/AustralianPoliticalRadioInfluence2026Exact.agda` now explicitly distinguishes KSL legal registration, self-reported retained ownership, producer AIIMS, Nine↔Tapt commercial association and a **proposed** ARN buyout. Prior Bannon–Palmer canonical owner remains only in PR #1131.

**End-state:** no identified external Sandilands investor currently established; documented commercial distribution/revenue-share and in-house operating structure; specific ABC Ombudsman editorial failures established; 2024 alleged threats and message authenticity contested; three Bondi events remain strictly typed. Future direct receipts can update this graph without conflating network adjacency with a coordinated operation.

### Additional equity-audit discovery: presenter-service companies did own ARN shares

The 2025 ARN Media annual report's **share register as at 3 February 2026** contains two exact company-level entries: **Quasar Media Services Pty Ltd: 3,161,166 shares, 1.01%** and **Henderson Media Pty Ltd: 3,161,166 shares, 1.01%**. Original company annual report reproduced as HTML https://financialfilings.com/filings/arn-media-limited/annual-report/2026/37381126/ . ARN's own **18 March 2026** termination notice https://arn.com.au/market-announcement-termination-of-contract-with-quasar-media-and-mr-sandilands/ identifies Quasar as the Kyle broadcasting-services contractor. Its **3 March** announcement https://arn.com.au/market-annoucement-the-kyle-jackie-o-show/ identifies Henderson Media as Jackie's separate services firm.

This supplies direct **historic contractor ↔ old-broadcaster equity** evidence, far stronger than speculation about a billionaire investor in KSL. It does **not** show either firm still held those shares in October after the termination/settlement, nor does it convert a share in ARN into a share in Kyle Sandilands Live Pty Ltd. The contractors' ultimate beneficial owners, share class/vesting and disposals are not established by this top-twenty list. A February register is an equity **snapshot**, not a perpetually valid ownership claim.

The same ARN report lists **Samuel Terry Asset Management 71,169,009 shares**, **Seven West Media Investments 45,517,739 (14.54%)**, **Grant Broadcasters 35,934,891 (11.48%)**, plus nominee holdings. ACMA's February 2026 media-interest notice https://www.acma.gov.au/updates-media-interests-snapshot tracks **Seven West being acquired by Southern Cross Media Group** and its continuing **14.54% ARN interest**, while **SGH/Kerry Stokes** held approximately **20.06% Southern Cross**. That is a real two-tier equity relationship, not an editorial-instruction pathway.

**Latest SGH revision (important date correction):** The February 2026 ACMA figure of **20.06%** in Southern Cross was superseded by ACMA's **11 September 2026 revision to 23.19%** for SGH/Kerry Stokes. Original regulator log: https://www.acma.gov.au/updates-media-interests-snapshot . These are two time-sliced exposures, not additive stakes. The indirect Southern Cross -> ARN **14.54%** position is documented by the February update; no later revised ARN percent was located in the regulator changelog. The second-order path therefore uses 23.19% (Sep) to Southern Cross and 14.54% (Feb documented) to ARN, with individually dated edges and no implied multiplication into editorial influence.

**Conflicting News Corp historical records:** ACMA says News Corp Australia **ceased** substantial-holder status in ARN December 2025; ARN's annual-report substantial-holder table labelled 3 February 2026 still names `News (Sydney) 43,736,386`. Public aggregators also often show 13.97%. These cannot all be treated as one verified **October** beneficial holding. Resolve via original substantial-holder cessation notice and effective dates; don't assert either that News definitely still directs ARN or that it has zero residual share exposure. Share-register nominee, substantial-holder and ultimate-control entities need distinct definitions.

### Formal change from earlier investor reasoning

- `newShowLegalOperator` → **legalOperatorRegistration** (ABR proves operator exists, *not* ultimate equity)
- `quasarARNHistoricalEquity` / `hendersonARNHistoricalEquity` → **historicEquityHolding** (February 2026 snapshot only)
- `southernCrossARNIndirect` / `stokesSouthernCrossStake` → two separately sourced equity edges (no transitively inferred editorial control)
- `aiimsProduction` → **productionSupply** (not equity)
- `nineTaptStrategicPartnership` → **announcedStrategicPartnership** (not continued shareholding and not proof every announced collaboration executed)
- `kyleProposedARNBuyout` → **proposedUncompletedAcquisition** (reporting ≠ completed financing)
- `arnSandilandsRevenue` → **financialEntitlement**, explicitly 19.9% **net revenue** conditional, not equity

This is a productive second-order outcome: owner topology, former presenter equity, production chain, licensing, residual revenue incentives and direct political messaging are all distinct object kinds that can feed actual network tests, without claiming one hidden command structure.


---

## 24 October 22:53 Brisbane: Google AI Mode intake failure / primary-owner progress

### External shared-conversation intake: initial failure on 24 October (SUPERSEDED by 25 October uploaded transcript)

Submitted user link: `https://share.google/aimode/Ux4UtsL535FOH9STw`.

**Acquisition attempt**: browsing direct open returned `DisabledError`; public searches of the literal share ID yielded no content-bearing result. A separate direct connection did not resolve the URL in the isolated runtime. Google's own description at https://share.google/ confirms that share.google is an app-oriented redirect; Google Search Help https://support.google.com/websearch/answer/16517651?co=GENIE.Platform%3DAndroid&hl=en-DE explains that AI Mode shares can expose an entire thread and are user-managed. The presence of a shared link **does not** establish what its answers say. No source claim, citation, transcript, external-file hash or actor edge is created from this inaccessible link.

**Priority**: conditional P0 only when the user supplies the rendered AI Mode text, an export (.md/.txt/.pdf), or screenshots containing actual answer and citation URLs. After that, each original cited source must be acquired separately, with the AI Mode answer retained as a tertiary *discovery* surface. Do not reverse-engineer supposed contents from the topic of surrounding discussion, and do not fabricate an AI Mode citation.

### First-party original ABC Ombudsman executive summary acquired through web

Original publisher listing: https://www.abc.net.au/about/ombudsman/activity-reports/four-corners-ombudsman-investigation-exec-summary/107181998 . Original **five-page PDF**: https://live-production.wcms.abc-cdn.net.au/39e8eeeffed7acde9a54d3ccc2f2a6fb .

**Signed by Fiona Cameron 20 August 2026; publicly posted 22 September 2026.** Pages 1–3 visually inspected. Contains actual findings, recommendations, methodology (broadcast originals, transcripts, fact-check paperwork, scripts, internal correspondence; eight formal interviews), and annexure with 1 July Board terms of reference.

| Finding | Original report page | Exact documented editorial defect | Standard |
| --- | --- | --- | --- |
| F1 | 1 | One person appeared in two significantly different ways in *Cocaine Nation*; viewers misled | accuracy 2.2 |
| F2 | 1 | Source “Jason” was not reasonably verified as a trafficker, nor were his substantive claims, while the programme presented role/account as fact | accuracy 2.1, 2.2 |
| F3 | 2 | Disguise/anonymity of the “sweeper” was not escalated for senior approval | fair and honest dealing 5.9c |
| F4 | 2 | Source “Brendan” identity/cook status and reporter relationship in *Meth Highway* insufficiently independently checked/disclosed | accuracy 2.2 |
| F5 | 2 | Cumulative source, approval, fact-check and management oversight failures misled the audience across both programmes | independence/integrity 1.1 |

Original seven recommendations (pp2–3): R1 remove both programmes; R2 broader investigation; R3 visible correction; R4 clarify standard 5.9, responsible senior anonymity approver and source context; R5 train legal-risk versus editorial-risk distinction; R6 strengthen fact-check and upwards referrals; R7 support junior teams working on high-risk programmes.

**Important difference:** ABC's 22 September institutional response https://www.abc.net.au/about/media-centre/statements-and-responses/abc-response-to-ombudsman-review-of-cocaine-nation/107182808 says all seven were **accepted** and implementation was complete or underway. The executive summary itself does not independently certify completion of all seven. The PDF's terms of reference investigate **editorial source misrepresentation**, NOT whether Fazal transmitted criminal threats or authored the 2022 Shanks firebombing. Existing source-owner constraints remain intact.

**Code changes**: `FriendlyjordiesABCFazalSourceAudit2026Exact.agda` now owns `ombudsmanOriginalExecutiveSummary`, 5 finding rows with source/standard/page coordinates, and 7 separate recommendations with institutional acceptance separated from verified completion. Its validation file provides source-specific equation witnesses and a negative acceptance→independent-completion boundary. No additional governance ontology invented.

### Source-level KSL venture financing detail: who actually funded launch?

The strongest **first-person interview**, Steve Ahern, RadioInfo **28 July 2026**:
https://radioinfo.com.au/news/weve-already-got-the-bills-paid-for-the-next-two-and-a-half-years-kyle-sandilands-new-show/ .

Kyle says the business had tens of thousands of prepaid subscribers (reported close to **AUD 2 million**, pricing approximately AUD 100/year) and that Bruno Bouchet said this could cover their planned costs for about **2.5 years**. These are **un-audited self-reports**; neither original bank statements nor subscriber ledger, refunds, currency variation, cost budget, churn or net sales are available. Subscription prepayment is **customer financing**, not the sale of shareholder equity.

The same interview reports potential prize/promotional support from **Harvey Norman** and approaches by two electric-car companies. These are Kyle's attributed statements describing **approaches**, not independently proved signed contracts, in-kind consideration, share investment, direct political funding or delivery of vehicles. Kyle also identified **Uscreen.tv** as technology underlying the cross-device streaming service; a vendor relationship, not a named shareholder.

His interest in a possible future platform carrying other presenters was explicitly **aspirational**, not a report of completed external-host onboarding. Earlier billionaire-investor approaches likewise were not accepted, according to his own interview. **The only evidenced completed outside-commercial-rights arrangement remains ARN's June public settlement** (conditional 19.9% **net revenue** entitlement, advertising allowance), distinct from both subscriber revenue and direct shareholder investment. Operator ABR registration still does not establish exact current share register.

**Cross-pollination**: `AustralianPoliticalRadioInfluence2026Exact.agda` now types `kyleSubscriberFinanceSelfReport`, `harveyNormanProspectiveSponsorship`, and `kyleUscreenPlatform` separately, with no automatic conversion of self-reported subscribers into audited sales, or prospective sponsor interest into equity. Its validation and the source-guard Python test enforce the provenance boundaries.

### Remaining max-cut (costed, no speculative network completion)

- **P0/source truth now closed**: original ABC Ombudsman executive summary located, visual pages checked, standard-specific findings and recommendations represented. This does NOT mean all historical ABC/2014-warning questions are closed.
- **P0/financial categorisation closed**: KSL customer prepayments, ARN contractual net-revenue interest, supplier/service providers, former ARN presenter-contractor shareholdings, third-party investment *approaches* and the actual KSL legal operator are represented distinctly.
- **P1/valuable original**: obtain the KSL company's ASIC historical/current member register (if available via appropriate lawful/public access), ARN notice on disposition of Quasar/Henderson's older shares, or specific signed sponsorship terms; these might alter exact current cap-table or campaign influence conclusions.
- **P1/ABC institutional outcome**: source-specific evidence documenting completion of recommendations R2/R4/R5/R6/R7; compare procedure in actual ABC 2024 complaint materials and 2026 oversight response, without assuming criminal liability.
- **Conditional on content availability**: the submitted Google AI Mode shared thread. No content attached until its text is accessible. If supplied, parse all primary citations and assign each proposition to its original owner, with disputed summaries/copies given separate relation types.


---

## 25 October 2026: Google AI Mode transcript acquired; source-reconciliation cut

**Prior failed share-link acquisition is superseded for content access, not for original endpoint verification.** User supplied the Google AI Mode conversation as a UTF-8 text attachment, 60,685 bytes, 561 lines, SHA-256
`80b27d5b866a0a906142a6c66f3e090ad39342ecbe4173f088ef48ea61adbfcc`.
The advertised link is `https://share.google/aimode/Ux4UtsL535FOH9STw`. An original Google-hosted rendering was not independently obtained. The local text is a **user-provided copy of an AI-generated answer**; neither the answer nor its repeated citations independently corroborate the world's facts. Only a checksum and scoped lines/leads are retained here, rather than vending the complete unverified personal-allegation/gossip transcript.

**Formal ownership after consolidation:** date-bounded, independently sourced relationship receipts reside in `AustralianPoliticalRadioInfluence2026Exact.agda` with checks in `AustralianPoliticalRadioInfluence2026Validation.agda`. The Google AI Mode export is only an acquisition/provenance and lead ledger *here in Markdown*, not its own mathematical owner or independent evidence. Low-evidence leads remain documentary rather than receiving proof wrappers. Original Bannon–Palmer source and denial stay owned by **PR #1131**, `BannonFaragePalmerAutomatedInfluenceReceiptsExact`; no competing EFTA01615861 source body is installed. The acquired transcript is a **query provenance root**, not a source root independently establishing a payment, meeting or offence.

### Distilled lead-to-source joins (not one connected conspiracy)

| AI Mode location (1-based upload lines) | Claim being checked | Independent source and actual permitted conclusion |
|---|---|---|
| 476-502 | Rinehart directly near Bannon at 2024 Miranda Devine NYC event | Daanyal Saeed, Crikey, 6 Nov 2024, https://www.crikey.com.au/2024/11/06/australian-conservatives-normal-us-election/ independently reports both in attendance. Proves event co-presence *as reported*, not a private contract/strategy role. |
| 492-495 | Advance's Sheahan conducted strategy meetings with Bannon | Mike Seccombe, The Saturday Paper, 7 Feb 2026, https://www.thesaturdaypaper.com.au/news/politics/2026/02/07/did-steve-bannon-stop-labor-winning-2019 says he was 'spotted chatting' in Washington. **Do not upgrade a reported chat into strategy meetings or instructions.** |
| 297-300 | Rinehart financed nearly 10% Southern Cross stake | Guardian 27 May 2026 https://www.theguardian.com/business/2026/may/27/gina-rinehart-pays-for-bruce-mcwilliam-purchase-southern-cross-media and Denis Muller https://www.thenewdaily.com.au/news/politics/australian-politics/2026/06/11/media-politics-influence: ~AUD26m lending to McWilliam, near-10% stake, relevant voting/security interests and contingent share control, not identical to direct, unencumbered ownership or a newsroom order. Discrepant 9.15/9.5/9.73% descriptions require same-date filings. |
| 291-295, 244-249 | Rinehart secretly funded Karl Stefanovic podcast; later internal ownership dispute | **The Australian's** `The Front` 29 Jun 2026 AEST (28 Jun UTC) https://podcasts.apple.com/za/podcast/did-the-ben-roberts-smith-drama-end-karl-stefanovics-career/id1614339406?i=1000774589371 says Rinehart **'appears'** to have bankrolled it. No contract/amount presented. Separately September court evidence establishes Stefanovic and Ibrahim-side stakes in 123 Podcast; AAP/RadioInfo Oct reports confidential buyout https://radioinfo.com.au/podcast-info/karl-stefanovic-podcast-to-resume-unfettered/ . Investor, advertiser, lender, principal and production co-owner are separate positions. |
| 484-502 | Rinehart bought $8m Brisbane headquarters and 'gifted' it to Hanson | ABC and AAP, 5 Oct 2026, https://aapnews.aap.com.au/news/one-nation-to-shuffle-deck-rent-gina-rinehart-office : building held by Rinehart-linked entity, to be **leased** to One Nation, with party/Hancock saying commercial rent. The **gift of building title** is not supported. Actual lease schedule not independently inspected. |
| 84-88, 122-126 | Stefanovic left Nine after Robinson interview; Hanson redistributed episode | ABC 24–26 Jun 2026 https://www.abc.net.au/news/2026-06-24/karl-stefanovic-tommy-robinson-podcast-interview-taken-offline/106834832 and https://www.abc.net.au/news/2026-06-26/karl-stefanovic-leaving-channel-nine-9/106835046 . Publication, post-removal Hanson reupload, and Nine's confirmed departure are evidenced. Neither direct Bannon sponsorship nor editorial orders are. **Original interview-file-transfer method is unresolved**, not proof of secret direction. |
| 525-547 | Alan Jones's Gillard remarks and advertiser pressure | Contemporaneous ABC 30 Sep–1 Oct 2012: https://www.abc.net.au/news/2012-09-30/jones-says-pms-dad-27died-of-shame27/4287770 and https://www.abc.net.au/news/2012-10-01/sponsors-walk-away-from-under-fire-jones/4288740. Audio reporting and Jones's apology substantiate speech and advertiser reaction. Not evidence Bannon invented or directed a 2012 tactic. |
| 285-289 | Rinehart erased web references to Jones in 2024 | Original SMH reporting summarised by https://www.mediaweek.com.au/media-roundup-alan-jones-supporters-waiver-could-hadley-give-evidence-star-reporters-creepy-jones-interview-guardian-investigates-kyle-and-jackie-o-vulgar-content/ . Dated removal is reported; avoid guessing instruction, motive or altering the status of legal allegations. |
| 432-460 | Rudd attended Epstein function; alternatively denied contact | ABC 31 Jan 2026 https://www.abc.net.au/news/2026-01-31/kevin-rudd-refred-to-in-latest-epstein-files-dump/106290858 : third parties proposed meetings and a calendar mentioned Rudd; the ABC saw no direct contact. His office denied an introduction but acknowledged a **dinner at Jagland's home**, a distinct event. Do not promote a prospective guest list into actual Epstein meeting or wrongdoing. |
| 458-460 | Epstein / Mandelson connected to 2010 anti-Rudd mining tax campaign | ABC Ben Butler 2 Feb 2026 https://www.abc.net.au/news/2026-02-02/peter-mandelson-on-rudds-mining-super-profits-tax-epstein-files/106295236 reports original released email: Mandelson forwarded Epstein Xstrata boss Mick Davis's anti-tax campaign analysis and discussed coalition/compromise. This is a **genuine same-object international information path**. It does not establish Epstein funded or ran Australian advertising, nor that he caused Rudd's removal. |
| 344-349 | Bannon said he directed Palmer's AUD60m 2019 China/climate advertising | **Existing PR #1131 source root only**: DOJ EFTA01615861 with Bannon's attributed text; Palmer acknowledged a call but denied Bannon directed the campaign. Avoid duplicate case or promotion to verified operational leadership. |
| 401-416, 373-378 | Murdoch's alleged black-book entry means Jones/Fordham knew Epstein; Epstein jets never visited Australia; no Australian associates named | **Unverified/exaggerated in the Google transcript**. An address-book mention, even if authenticated, cannot prove contact with broadcast talent, a personal meeting, or criminal participation. A non-exhaustive flight database cannot establish a total absence of social overlap. No categorical negative 'none of the Australian network' claim admitted. |
| 140-143, 128-132 | Kyle/Karl joint domains; cyber-bot attacks by several governments | Treat as attributed rumour or self-report pending independent registry/time-series/cyber-forensic evidence, not operational fact. |

### Additional second/third-order join discriminators

1. **Ownership/control layer:** time-stamped 2GB/Tapt/Laundy, KIIS/ARN, Southern Cross–ARN, SGH/Stokes, McWilliam financed Southern Cross interests, Quasar/Henderson historical ARN shareholdings, and Stefanovic's 123 Podcast private equity are *different dated legal relations*. Multiplying economic percentages across companies is **not** a valid proof of transitive voting control or direct orders to journalists.
2. **Message layer:** Stefanovic original publication → Hanson re-publication has a dated content object, in contrast to the generic 'Bannon playbook' analogy. Acquire exact upload/video hashes, authorship, permission and transcript; determine whether Hanson obtained a copy from Karl's public channel or an independent transfer before inferring coordination.
3. **Resources/tax correspondence layer:** the 2010 Mandelson→Epstein forwarding of Xstrata content is stronger than social-proximity graph chatter; source the original DOJ message ID and trace same-document recipients/transactions. **Do not collapse** the 2010 anti-RSPT campaign with the 2019 Palmer advertising into one operation just because both involved resources politics.
4. **Third-party mention layer:** Rudd/Epstein email and calendar references, denials, and Rudd's IPI remedial activity are typed separately. No negative proof of global nonassociation, nor positive proof of contact or wrongdoing, follows from one source list.
5. **Historical comparative media layer:** 2012 Jones/Gillard broadcaster–advertiser boycotts, 2026 Sandilands/MFW advertiser pressure, and ABC/Friendlyjordies institutional verification are distinct episodes. Comparison may yield testable recurrence of commercial incentives and pressure, not invented personnel continuity.
6. **Next receipts, by information gain:** company/ASIC extracts for 123 Podcast and KSL, source of any Rinehart→Stefanovic payments or sponsorship, 2026 McWilliam security deed and latest beneficial ownership, exact Bannon/Rinehart 2024 event records, and the DOJ ID for the Mandelson/Xstrata correspondence. Do not divert from the remaining BOM original climate-audit and Fordham spoken-audio source gaps.

**Status:** This appendix is an evidence-graded intake of a user-provided AI answer, not endorsement of its gossip. Existing `AustralianPoliticalRadioInfluence2026Exact.agda` records the selected source-checked relationships and existing non-promotion guards; low-value rumours remain unresolved documentation, not formal source facts. No Agda kernel check or exhaustive review of every name in the 561-line shared answer is claimed.

### Supplemental audit of earlier gossip (not party-control evidence)

- **MFW advertiser boycott, Google export lines 30-39:** first-party https://www.mfw.org.au/our-campaigns/ details the #VileKyle tactic; the Guardian's **9 Oct 2024** reporting https://www.theguardian.com/media/2024/oct/09/kyle-and-jackie-o-show-advertisers-back-out-violent-misogyny-accusations-campaign-mfw-ntwnfb confirms named sponsors withdrew or reviewed placements. Jennie Hill's larger hundreds/thousands-of-brands and AUD30–40m loss estimates, in https://www.moneymag.com.au/the-daring-activists-targeting-kyle-and-jackie-o-advertisers, are **MFW estimates**, with alternative reasons for ad spend movements acknowledged by Hill. None is a Steve Bannon link.
- **The 'Kyle & Karl' shadow venture, lines 140-143:** https://www.news.com.au/entertainment/celebrity-life/best-7-i-spent-wild-truth-behind-kyle-and-karl-show-finally-revealed/news-story/67b17fe0f26e56c5d002df9c1f8f22cb reports Bruno Bouchet publicly claimed to register two joint-brand domains for around AUD7 to generate gossip. The registrations, if independently checked in historical WHOIS, would still be **domains, not a funded company or programme**.
- **The Alan Jones abrupt interview cut, lines 172-177:** https://qnews.com.au/secret-alan-jones-recordings-before-kyle-jackie-walkout/ reports the Kyle & Jackie O cut to nine minutes of advertising as Jones discussed off-air tapes. There is **no verified content** for the unbroadcast portion, hence no justified claim about what was being hidden.
- **Rupert Murdoch and Epstein address book, lines 399-405:** the secondary name index https://epsteinsblackbook.com/names/rupert-murdoch says page 39 contains Rupert Murdoch with two telephone numbers. An authenticated primary facsimile/context check is preferable; even authenticated inclusion is not direct acquaintance, participation in offending, or Alan Jones/Sandilands contact.
- **Historical source origin:** Alan Jones's abusive 2012 Gillard remarks and advertiser response predate MFW's organisation, Kyle's 2026 independent venture and the 2019 Bannon-Palmer correspondence. Similar advertising-boycott tactics cannot establish continuity of operators without a dated transfer receipt.


### 25 October max-cut consolidation: no source-specific Agda file

The two temporary `GoogleAIModeMediaClaimIntake2026{Exact,Validation}.agda` modules have been deleted from PR #1251. Eleven source-checked relationships were relocated into the existing **AustralianPoliticalRadioInfluence2026Exact** owner, and thirteen narrow regression witnesses joined **AustralianPoliticalRadioInfluence2026Validation**. The original user-provided AI answer is a *research prompt* with a hash and source-line references above, **not** a domain whose name belongs in the Agda module hierarchy. PR #1131 retains sole Bannon–Palmer ownership.

**Deliberately left documentary-only:** Rupert Murdoch black-book secondary index (not a contact/meeting), Kyle–Karl domain prank (not a company), the Jones interview cutoff (unbroadcast material cannot be reconstructed), Rinehart/Jones corporate website scrub (motive not established), and third-party Rudd-Epstein mention/denial (not directly a political-radio business relationship). Their links remain above for audit; no second weak graph is constructed around them.

The source map uses three layers: (1) source-provided/generated claim, (2) independently attributable publication or primary record with date, (3) typed edge only where a bounded relationship contributes to this case. Extra generic empty propositions were collapsed onto existing non-promotion types; remaining specialised guard types are explicitly syntactic distinctions, not external-world theorems.

---

## 25 October 2026 — Woogaroo/Springfield gas, climate denial source concentration and Project 2025 cross-pollination

**Scope / owner discipline:** This is a *cross-case consumer*, not a new corporate-history Agda module. Read the original owners (at **master** before concluding): `DASHI/Law/SensibLawSpringfieldGasLobbyingOwnershipSnowballExact.agda`, `SensibLawSpringfieldResidentialGasEndpointLockInExact.agda`, `SensibLawAzureSpringfieldInducedGasDemandExact.agda`, `SensibLawSpringfieldFirstNineApprovalGasEndpointBridgeExact.agda`, `DASHI/Governance/HansonCapacityCriticismHyperformalismExact.agda`, `ClimateGenealogyTypedCasesExact.agda`, `EvidenceGradedGenealogyCasesExact.agda`, `DASHI/Interop/GodsEyeViewDiagnosisDrivenActivistRollupExact.agda`, `GodsEyeViewWorldEpistemicSourceAtlasExact.agda`, `DASHI/Wikimedia/IbrahimSnowballAnthropologyClimateDenialPoliticalTheologyExact.agda`, and `DASHI/Core/InstitutionalProximityInfluenceAdequacyExact.agda`. Existing PR #893 owns the original Springfield gas/lobbying work; PR #561 the typed empirical genealogy. Do **not** mirror those source receipts as new donations, lobbying records, or political influence proofs in this radio case.

### Actual local-economic chain (documented versus residual)

1. **2004 gas infrastructure planning.** ABC journalist's **30 Apr 2004** contemporaneous report: https://www.abc.net.au/news/2004-04-30/development-aims-to-set-alternative-energy-use/178340 describes Energex–Springfield Land Corporation gas-and-electricity alliance and CEO Greg Maddock's statement referencing **8,000 gas connections** and common trenching. This is a contemporaneous planned/network opportunity, not the original contractual alliance, an actual completed-customer count, or today's Allgas/APA ownership.
2. **Development actors and political access.** The dedicated Springfield owner cites Azure Development Group ABN **67 600 740 163**; Chris Schroor's reported historical Springfield employment and later Seasons/Ember/Oakmont partnerships; Queensland Electoral Commission's **$15,000 11 Feb 2019 and $10,000 15 Mar 2019** gifts by Azure Development Group to the Queensland LNP; and the **4 Feb and 12 Feb 2025** ministerial diary interactions identifying Santo Santoro and Springfield parties. Each is an independent personnel/partnership/donation/meeting fact. No donor-to-gas-policy causal edge, gas-specific lobbying brief, current private beneficial-control record, or developer kickback is paid. Preserve ABN collisions between *Azure Development Group* and unrelated Azure-named companies.
3. **Actual endpoints.** The residential owner records de-identified investigator observations of instantaneous gas hot-water, mixed gas/electric cooking and rooftop solar. The induced-demand owner distinguishes an actual connection, fixed customer tariff exposure, gas throughput, appliance specification, hot-water dead-leg losses and network asset utilisation. These are **plausible demand-retention mechanisms**, not audited metered demand, financial benefit or evidence that the developer deliberately pursued gas lock-in. Required exact objects: project inclusions/hydraulics, MIRN/distributor identity, gas-meter intervals, tariffs, asset-register chain and electricity/gas life-cycle counterfactual.
4. **Commercial policy join: September 2026 One Nation gas reversal.** `HansonCapacityCriticismHyperformalismExact.gasReservationResidual` already owns the reported **March support → June opposition** shift on domestic gas reservation after industry consultations. Guardian (14 Sep) https://www.theguardian.com/australia-news/2026/sep/14/one-nation-pauline-hanson-abandoning-gas-reservation-plan-gina-rinehart-relationship-ntwnfb explains alignment with the interests of **Senex, 49% Hancock Prospecting / 51% POSCO**; Senex denies undue influence, One Nation denies donor direction. This is a *more specific policy-benefit comparison* than generic radio ideological proximity. Missing: the full contemporary policy drafts and consultation/communication instruments, revenue and price consequences, counterfactual explanation. **No assertion that this particular national gas-reservation policy caused one Springfield appliance.** The residential planning began decades earlier.

### The original-denial-roots hypothesis: narrow and testable

- **Existing primary genealogy:** `ClimateGenealogyTypedCasesExact` records R.J. Reynolds → Frederick Seitz (actor account), Seitz → Marshall Institute (role), Marshall Institute named in the **1998 API Global Climate Science Communications Team Action Plan** (direct primary textual receipt), and similarity with the **1969 B&W tobacco memo**. Source-original overlap, personnel continuity and *technique transfer* are different edge types. The 1969↔1998 recurrence is well evidenced as a pattern; a direct intermediary transferring that precise method is still a residual, not a proven command chain. `Docs/support/reference/climate_genealogy_typed_edges.csv` calls this **E4 pattern recurrence A** versus **E4b transfer B/D pending bridge**, and warns against silently promoting Hill+Knowlton method transfer or Fred Singer payment evidence.
- **Independent empirical corroboration on Australian claims:** Carly Lubicz-Zaorski, Maxine Newlands and Theresa Petray, *Public Understanding of Science* (2024), DOI **10.1177/09636625231202117**, https://journals.sagepub.com/doi/10.1177/09636625231202117 tracked a 2021 Great Barrier Reef *AIMS* scientific report reframed by a **small, influential** group of commentators. Their actual case describes Peter Ridd's original *Australian* opinion reframed and re-amplified through Watts Up With That, GWPF/Net Zero Watch, Advance, Sky and other social media commentators. Do not sum reposts as independent originating science. Specific citations/links, not broad ideological labels, establish a lineage.
- **Taxonomy, not authorship attribution:** Travis G. Coan et al., *Scientific Reports* (2021), DOI **10.1038/s41598-021-01714-4**, https://pmc.ncbi.nlm.nih.gov/articles/PMC8595491/ classify contrarian climate claims as not happening, not human-caused, not harmful, solutions ineffective, or science/scientists unreliable. The BOM-to-conspiracy framing belongs to the last category as a possible textual coding, but **no single source origin, intention or coordinated instruction** follows from a taxonomy category.
- **Denial-origin concentration is a hypothesis per corpus**, not a universal proof that *all* denialism has only a few unique roots. Distinguish **original empirical observation** (e.g., original handwritten BOM folio), **auditor/critic** (Berger/Sherrington report not yet acquired), **original broadcaster frame** (2GB episode), **syndication and clips** (not independent witnesses), **claim template** (e.g., 'scientists unreliable'), and **actual financial/production dependency** (separate proof). For a sampled corpus, cluster exact proposition+date+source object, then deduplicate derivative copies before estimating independent-root count.
- **Concentration metric:** with observed narrative share by identifiable original roots `p_i`, an exploratory effective-number metric is `N_eff = 1 / sum_i p_i^2` (Herfindahl reciprocal). Include an 'origin unknown' bin with uncertainty, sensitivity to coding/weighting, and distinguish numbers of *claims*, unique *text origins*, and financially independent *publishers*. Never claim a global numerical 'vanishingly small' root set without a defined corpus and acquisition.

### Project 2025: original chapter, proposed rule and realised policy must stay separate

Primary document is already owned by `GodsEyeViewWorldEpistemicSourceAtlasExact.heritageProject2025Primary` and `GodsEyeViewDiagnosisDrivenActivistRollupExact.project2025PrimaryPacket`, **Paul Dans and Steven Groves** (eds.), *Mandate for Leadership: The Conservative Promise* (Heritage 2023), https://static.heritage.org/project2025/2025_MandateForLeadership_FULL.pdf. The existing packet correctly requires **named chapter author** and **independently verified downstream implementation**.

- **Chapter 12** (Bernard L. McNamee, Energy/DOE): explicitly advocates ending climate considerations in LNG export approvals, narrowing FERC's role as a climate regulator, and refocusing DOE on energy security and fossil resources; reproduced with historian annotations at https://envirodatagov.org/project-2025-department-of-energy-and-related-commissions-annotated/ . These are concrete *2023 US policy proposals*, not a dated decision by an Australian gas provider.
- **Chapter 13** (Mandy M. Gunasekara, EPA): characterises previous EPA climate policy as activist or ideologically co-opted, proposes limiting or reorienting regulatory scope, and frames climate regulation as an economic threat. Annotated text https://envirodatagov.org/project2025-environmental-protection-agency-annotated/ . It exhibits institutional-trust framing similar in *function* to the 2GB 'conspiracy' headline. Similar framing does NOT mean 2GB received a Heritage message.
- **2025 US implementation**: FactCheck.org October 2025 https://www.factcheck.org/2025/10/trump-project-2025-and-climate-change-fossil-fuels/ documents several Trump-administration fossil/climate measures and proposal to reverse the 2009 EPA endangerment finding; each policy outcome must be individually tied to its final-rule status, effective date, court result and the precise corresponding Project 2025 recommendation. A proposal is not a final rule.
- **Cross-border boundary:** functional convergence across Heritage, Australian broadcasters, Hanson, donor campaigners and local gas developers does *not* demonstrate direct transfer. A true method/coordination edge requires a dated joint brief, shared producer, source-text borrowings with directionality, payment, editorial instructions or traceable joint event/material.

### Highest-information max-cut, with both positive and negative discriminators

| Cut | Observable object | Positive discriminator | Counterexample / negative control |
|---|---|---|---|
| **P0 Claim-root compression** | Fordham audio/transcript, Berger/Sherrington original audit, BOM original response, repost URLs, 2021 reef article chains | Several outlets demonstrably copying the same dated unsupported inference or quoted paragraphs from one identifiable producer | Independently produced different claims, or journalist accurately attributes criticism while refusing to endorse fraud |
| **P0 Domestic gas policy change** | One Nation March/June texts, Senex policy submissions, Hancock contacts and contemporaneous meeting notes | Dated donor/industry recommendation materially matches changed text, and movement is temporally established | Independent publicly stated gas-supply reasoning predates contact; donors disagree with party or content is not transmitted |
| **P0 Springfield economic endpoint** | Historical Energex–SLC agreement, current network owner, Azure inclusions, gas connection, tariff, meter, new-build counterfactual | Same project/network/asset shows new gas connection and measurable fixed charges and throughput | Optional gas chosen solely by buyers; pre-existing legacy connection; no attributable net advantage or comparable electrification costs |
| **P1 Transnational policy template** | Heritage 2023 chapter spans, original 2025/26 US rules and Australian political drafts | Shared versioned text, personnel, briefings or financial relationship beyond independently common political positions | Mere analogy, contemporaneous independent development, policies diverge in detail or goals |
| **P1 Durable externalities** | Gas asset lives, capacity/connection numbers, rates, retrofit costs, emissions boundary, consumer choices | Incremental policy/design-induced demand and cost or emissions over asset life established quantitatively | Gas use declining irrespective of political framing; easy cost-effective electrification; consumer demand drives installation independently |

**Integrated conclusion:** In the available evidence, *a small number of recurring climate-doubt originators can be amplified many times*, politically influential donors and gas-industry arguments can coincide with demonstrable party policy changes, and built-environment choices can preserve gas revenue or demand. Yet the complete media → donor → policy → specific developer → asset → household causal chain has **not been established**. Bannon remains a useful search hub and IDW warning signal, not a required central agent. Woogaroo's separate environmental/EPBC approvals cannot be repurposed as proof of gas lobbying, and there is no single global conspirator field in the schema.

### Exact original-source first-pass join: May–October 2026 gas reservation

Following the prior secondary coverage, the actual **first-party policy texts** are accessible and more discriminating:

- **Senex 8 May 2026 CEO statement** https://senexenergy.com.au/news/statement-on-domestic-gas-reservation-policy/ objects that the proposed scheme undermines investment certainty for domestic-facing gas producers, encourages more production as an alternative, and argues it may reduce gas supply. This **predates One Nation's June policy**.
- **One Nation 9 June 2026 original gas-policy page** https://www.onenation.org.au/gas-policy-ownership explicitly acknowledges its earlier consideration of east-coast reservation, says industry/stakeholder consultation led it to reject the government's 20% proposal, characterises forced 'oversupply' as potentially harming Australian domestic gas producers, and calls for more exploration and production.
- **Senex 24 September 2026 submission** https://senexenergy.com.au/news/exposure-draft-domestic-gas-reservation-scheme-legislative-package/ reiterates opposition to domestic reservation and asks for amendments that protect domestic-focused suppliers and investment incentives. A later independent statement cannot establish the source of the earlier June words.
- **Senex 23 October 2026 contemporaneous statement** https://senexenergy.com.au/news/senex-calls-for-balanced-policy-to-support-gas-supply-investment-and-energy-security/ repeats objections to the reservation bill, describes falling producer returns as a transfer of economic value from gas producers to consumers, and calls for amendments. Current controversy should not be retrojected to prove June private consultation content.

**Inference classification:** There is a dated, policy-specific *argument overlap* between a gas producer part-owned by a major One Nation patron and One Nation's 9 June official policy. This is substantially more informative than common talk-radio conservative framing. The overlap has a direct competing explanation (both actors favour producer incentives and oppose the same government policy); it does not reveal that Senex supplied One Nation's text, arranged or attended the stated consultation, or paid for that policy. Obtain the party's consultation register, editing history and any Senex/Hancock correspondence for direct transfer. Compare the full proposals, not isolated matched words, and independently model impacts for domestic consumers/producer returns.


---

## 25 October 2026 — identify originating claims, copying chains and observable decisions

**A defined ledger, NOT a representative crawl:** `Docs/support/reference/australian_climate_claim_origin_edges_20261025.csv` contains **21 bounded relationship rows**, comprising 9 BOM, 8 Great Barrier Reef and 4 gas-policy edges. This is a **curated, source-qualified, non-exhaustive evidence graph**. Neither 21 publications nor nine BOM rows imply 21 independent producers; it is also **not** enough to estimate the share of all Australian climate-denial discourse arising from these actors. Do not use an inverse-Herfindahl diversity estimate until a prespecified, proportionately sampled corpus, transparent root resolution and exposure weights exist. For within-graph assertions, count *root authors of exact propositions*, not websites.

### Who actually originated what (producer, interpreter, distributor and institution are different)

| Bounded case | Distinct creator/source roots | Subsequent amplifiers or adopters | What is *actually* demonstrated |
|---|---|---|---|
| **BOM October 2026** | **Tom Berger/Geoff Sherrington**: attribution of an unacquired forensic audit and its pattern claims; **Graham Lloyd**: separately checked original Sydney Observatory ledger against digitised data; **Jennifer Marohasy**: her prior hypothesis and later published account; **BOM**: original observation keeper and 22 October first-party reply | **Jo Nova**, CFACT (Nova-hosted), Watts Up With That (Marohasy-hosted), Clintel (Marohasy-hosted), Climate Change Dispatch (Nova and Lloyd bylines), **Ben Fordham/2GB** (outside-audit broadcast frame) | Source-root authorship, publicly marked common author/byline, and a separately evidenced archives check. **Not** demonstrated: that Fordham copied a particular paragraph directly, author of his site's headline, auditor's complete code, or a single political command channel |
| **Great Barrier Reef July 2021** | **AIMS scientific survey and report** (qualified recovery data); **Sussan Ley's ministerial office** (accelerated release and selected-newsroom preview, evidenced by contemporaneous FOI emails); **Peter Ridd** (his own opinion reinterpretation in *The Australian* on 23 July); **Sky interview presenters** (additional editorial framing) | The Australian, Courier Mail, Sky News, Patrick Moore, Watts Up With That, GWPF/Net Zero Watch, Advance, Matthew Canavan and Paul Hanson comments; networks described in Lubicz-Zaorski/Newlands/Petray | **FOI-backed targeted government information release** is a particularly strong source-to-distribution edge. Peer-reviewed social-network tracing establishes content propagation, but **not** that Ridd or downstream actors were commissioned by government |
| **Domestic gas reservation May–October 2026** | **Darren Stevenson/Senex** on 8 May; **One Nation's policy authors** as publisher on 9 June; later **Senex** same-authority industry submissions | Other political and media commentary, not exhaustively sampled here | Specific publicly authored objections line up in policy effect and economic explanation; **actual transfer not established**, despite One Nation's independently published statement that gas-producer consultations occurred |
| **Historic tobacco→climate roots** | **1969 Brown & Williamson memo** (tobacco uncertainty strategy); **1998 API climate communications action plan** (a primary energy-industry plan); documented Seitz/Marshall continuity | Later advocates and think tanks; see existing `ClimateGenealogyTypedCasesExact` and `Docs/support/reference/climate_genealogy_typed_edges.csv` | Similar methods and selected personnel/organisational relations demonstrable; the precise 1969→1998 method-transfer instruction remains *unpaid* |

### Exact BOM claim lineage, with duplicate-origin compression

- **Berger/Sherrington → Lloyd** is a *reported source of the original anomaly search plus an independent archival checking step*. The report itself is still unacquired; the source and checking step must not be counted as the same eyewitness act. Jennifer Marohasy reports forecasting which August year had been copied before Lloyd's checking, but this forecast is a participant account, not evidence of coordinated production. https://clintel.org/australian-temperature-records-errors/ .
- **Jo Nova ↔ CFACT ↔ Climate Change Dispatch**: CFACT's **18 October** page credits Jo Nova and republishes Graham Lloyd content; Climate Change Dispatch **20 October** page identifies its author as Jo Nova. This provides a *visible author-origin collapse*, though no byte-for-byte text hash has been acquired. https://www.cfact.org/2026/10/18/boms-scientific-scandal-the-raw-data-is-not-raw/ and https://climatechangedispatch.com/the-on-going-data-tampering-by-australias-bureau-of-meteorology/ .
- **Marohasy ↔ Watts Up With That ↔ Clintel**: WUWT **19 October** credits Marohasy's account; Clintel **21 October** credits her. A later independent op-ed *authored by the same named person* may add facts or interpretation, but it is not independent confirmation solely by changing publishers. https://wattsupwiththat.com/2026/10/19/australias-historical-temperatures-update-following-tom-berger-forensic-audit/ and https://clintel.org/australian-temperature-records-errors/ .
- **Lloyd → Climate Change Dispatch** **23 October**: published as by Graham Lloyd, with original archive narrative; publisher multiplication ≠ ledger comparison multiplication. https://climatechangedispatch.com/more-on-the-ausralian-bureau-of-meteorology-data-tampering/ .
- **Fordham/2GB** **19 October**: an original published headline and broadcaster metadata attribute copied-temperature allegations to an outside audit. **Exact spoken transcript absent**, and an alleged conspiracy is not demonstrated by the corrected duplicated values. https://www.2gb.com/dodgy-data-weather-bureau-accused-of-climate-conspiracy/ .
- **BOM** **22 October**, retrospectively notes **19 October** corrections, 4 post-1910 months and <200 of >7 million observations: a *later institutional rebuttal*, not evidence Fordham possessed this response when recording. https://www.bom.gov.au/the-science-and-truth-of-australias-long-term-temperature-record .

**Bounded result:** repeat appearances by Nova, Marohasy and Lloyd across named web domains do **not** constitute as many independent initial investigative teams. This is a concrete same-author counterexample to raw outlet counts. The full origin of 2GB editorial language and any undisclosed financer remains unknown.

### Great Barrier Reef: evidence of an actual state-to-media release pathway

A newly relevant original investigative report is **Michael Slezak, ABC, 2 September 2021**, grounded in FOI-acquired 2021 emails/Teams messages: https://www.abc.net.au/news/2021-09-02/government-told-science-agency-to-rush-reef-report-release/100422190 . These show the **Ley ministerial office directed accelerated AIMS report publication** before the UNESCO debate and AIMS personnel prepared selected media previews for **The Australian/Courier-Mail**. AIMS and the government said the technical work was already complete and the timing request reasonable. The evidence supports a *timed information-release and targeted access decision*, **not alteration of the underlying coral measurements** or commissioning a particular opinion columnist.

Then distinguish:
1. **AIMS primary scientific report**: temporary coral-cover recovery and fragility/cyclone/heatwave caveats, rather than a broad permanent-safe-Reef claim. AIMS independent July 12 briefing: https://www.aims.gov.au/information-centre/news-and-stories/great-barrier-reef-not-fine-and-nor-it-dying-truth-inbetween .
2. **Peter Ridd 23 July 2021 original column in The Australian**: the alternative institutional-reliability interpretation traced by **Carly Lubicz-Zaorski, Maxine Newlands and Theresa Petray** (first online 26 Oct 2023, journal issue April 2024), DOI **10.1177/09636625231202117** https://journals.sagepub.com/doi/10.1177/09636625231202117 . Their *six-week* 2021 corpus documented amplification by Patrick Moore, Sky, Watts Up With That, GWPF/Net Zero Watch, Advance and others. It does **not** declare these authors and organisations one coordinating conspiracy.
3. **Regulator's independent determination**: ACMA's **26 April 2023** *Outsiders* accuracy/representation findings in 3 licences: BI-645, BI-646 (regional) and BI-647 (subscription accuracy and distinguishability). https://www.acma.gov.au/investigations-tv-broadcasters ; this is a **specific published broadcast-standard breach**, not a general verdict about all content or every associated person.
4. **Separate empirical negative control**: AIMS later reported southern coral-cover decline in **2022**, and in **August 2025** substantial region-wide declines associated with marine heat stress. Those later data can test claims of permanent recovery, but cannot establish what a journalist knew in July 2021. https://www.aims.gov.au/information-centre/news-and-stories/highest-coral-cover-central-northern-reef-36-years and https://www.aims.gov.au/sites/default/files/2025-08/Media%20release%20AIMS%20Great%20Barrier%20Reef%20Report%206th%20August%2025.pdf .

### Producer-industry argument vs party policy: real overlap, more than one policy object

**8 May 2026 Senex CEO Darren Stevenson:** https://senexenergy.com.au/news/statement-on-domestic-gas-reservation-policy/ explicitly objects that reservation would undermine domestic producers, investment and competition, pushing lower rather than higher domestic supply.

**9 June One Nation's own policy:** https://www.onenation.org.au/gas-policy-ownership explicitly says it *previously considered* east-coast reservation and *consulted with industry*. It raises many of the same concerns over a 20% reservation policy harming domestic-only producers and causing oversupply. Its *additional*, party-specific proposals include **30% exploration rebate paired with up-to-30% public licence equity, ANWIC, six-month approvals, PRRT reform and abolition of the Safeguard Mechanism**. That means it is not a verbatim republication of Senex's 8 May statement.

**Interpretation:** The economic argument overlaps with the disclosed interests of a Hancock-part-owned producer. It may have arisen through actual consultation, common public industry reasoning, or independent political choice. At present, **actual transfer not established** and no Senex→One Nation paid-policy-drafting or command edge is admitted.

### What actually changed versus what has *not* been measured

| Object | Directly observed or documented | Missing causal/object identity |
|---|---|---|
| BOM daily records | BOM admits isolated transcription duplicates and says it issued a correction | Same-row pre/post dataset and reproducing the trend estimate; intent claims unsupported |
| Reef scientific release, July 2021 | FOI-supported accelerated release and selected newspaper preview | Whether release timing *caused* World Heritage votes; separate later editorial commissions |
| Reef broadcasts | Sky content assessed by ACMA, three specific licensing determinations | Subscriber persuasion, public-opinion change and downstream policy caused by broadcasts |
| One Nation June gas policy | Original policy explicitly documents changed position and industry consultation | Specific consultation participants, advice, internal versions and net policy benefit |
| Springfield residential gas | Developer/network historical records and household gas features in existing owners | Same-project planning instrument, current asset/distributor, tariff, consumption and measured incremental benefit |

### Root-of-claims inquiry: operational next cut

For each case, resolve (i) **original measurement**, (ii) **first claimant/analyst of the disputed interpretation**, (iii) **first publication and material framing**, (iv) exact verbatim reprint, attributed derivative or separate analysis, (v) sponsor/producer contract if established, (vi) actual decision and dated implementation, (vii) quantitative counterfactual effect. Require independent underlying evidence, not mere agreement or identical premises.

**Positive controls:** Slezak's FOI media-release chain; public Senex/One Nation policy originals; regulator determination; same named authored reprints. **Negative controls:** AIMS independently measured recovery that still included warnings; publisher-hosting without independent research; equivalent energy policies with independent rationale; later refutations not known to early speakers.

**Don't confuse three 'smallness' propositions:** few authors in a studied amplification cluster; few independently reproducible measurements supporting a disputed claim; and few controllers capable of directing media institutions. Only the first is partially demonstrated in the cited Reef corpus. The last is neither proved nor measured by the 21-edge ledger.
