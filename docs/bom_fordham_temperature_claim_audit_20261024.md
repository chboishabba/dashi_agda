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
