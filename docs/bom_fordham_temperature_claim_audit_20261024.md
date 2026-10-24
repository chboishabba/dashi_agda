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
- **Bannon–Palmer 2019**: DOJ-released Epstein-associated texts attribute to Bannon a first-person statement claiming authorship of Palmer's $60m China/climate attack ads. Palmer's spokesperson denied this: https://www.theguardian.com/us-news/2026/feb/02/clive-palmer-denies-steve-bannons-claim-he-was-behind-billionaires-controversial-2019-australian-election-ad-strategy . Strong evidence that this **allegation was made**, not independent proof the claimed 2019 coordination occurred; see open PR #1131's prior `BannonFaragePalmerAutomatedInfluenceReceiptsExact` to avoid duplicate historical ownership.

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
