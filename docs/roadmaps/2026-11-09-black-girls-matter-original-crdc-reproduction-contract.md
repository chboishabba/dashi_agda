# Black Girls Matter — original CRDC 2011–12 reproduction contract

Date: 2026-11-09. Scope: K1–K3, excluding kernel/ITIR work.
Owner policy: CRDC primary data belong to U.S. Department of Education Office for Civil Rights. The 2015 Black Girls Matter interpretations and specific charts belong to Crenshaw with Ocen and Nanda/AAPF-CISPS. The arithmetic verification Agda modules are DASHI-original, not source-authored proofs.

## Grounded original-source locations

- Official Department of Education CRDC historical data overview: https://www.ed.gov/laws-and-policy/civil-rights-laws/civil-rights-data-collection-crdc/civil-rights-data
- Official CRDC downloads: https://ocrdata.ed.gov/data ; the site lists "2011–12" as a downloadable historical data file and data definitions/notes.
- Historical exact ZIP URL listed in a third-party URL-monitor record, **not downloaded or hash-verified**: https://civilrightsdata.ed.gov/assets/ocr/docs/2011-12-crdc-data.zip
- Original 2011–12 definitions (DOCX, not read or hash-verified): https://civilrightsdata.ed.gov/assets/downloads/CRDC-Definitions-2011-12.docx
- Original 2011–12 data notes (PDF, not read or hash-verified): https://civilrightsdata.ed.gov/assets/for-researchers/data-notes/Data-Notes-CRDC-2011-12.pdf
- Primary report text: https://www.law.columbia.edu/sites/default/files/2021-05/black_girls_matter_report_2.4.15.pdf

## Reproduction decisions required BEFORE producing per-student risk

1. Preserve official download response bytes, SHA256, file inventory, source timestamp and CRDC data version. Search tool discovered the path; no local bytes were acquired this pass.
2. Identify the official LEA IDs for Boston Public Schools and NYC DOE for the relevant *2011–12* tables. Verify that the study's reporting units match district boundaries, exclusions and suppressed values.
3. Identify the exact discipline indicator codes used in the 2015 study for each district. The methods differ: Boston includes out-of-school suspension, expulsions, law-enforcement referrals and school-related arrests; NYC uses in-/out-of-school suspensions, expulsions and referrals. These cannot be equated without same-indicator filtering.
4. Identify whether source output is people disciplined once, events, episodes, or cumulative disciplinary actions; preserve unit and deduplication semantics. The 2015 report presents aggregate counts and uses "cases" for its relative comparisons.
5. Extract *same academic-year and district, race-and-gender disaggregated* enrollment denominator, same observation window and eligibility/suppression rules. The report's printed **2013–14 Table 1** must not be silently used to divide **2011–12 discipline numerators**.
6. Compare raw official row sums and source definitions against the reported Boston counts (Black girls 340; white girls 30; Black boys 637; white boys 81) and NYC counts (Black girls 9,076; white girls 884; Black boys 13,823; white boys 2,541). If mismatch, report discrepancy; never overwrite the report's sourced number without documenting the error model.
7. Treat figure 3/4 rounded race/gender shares independently from raw counts; report rounding uncertainty. No exact probabilities follow from rounded graphs.
8. Treat white-girl expulsion zero as actual observed denominator. Ratios 53:1 NYC / 10:1 Boston are illustrative one-count comparisons, not observed positive-denominator ratios.
9. Maintain disability/LEP omission and participant-voice safeguards; no inference to school-to-prison *individual trajectories* or psychological exhaustion without distinct consented longitudinal and causal evidence.

## Existing source-written formal results (Agda verification excluded)

- DASHI/Governance/BlackGirlsMatterPublishedDisciplineArithmeticExact.agda: four count identities, two rounded-share cross-products, two-period mismatch and an external raw-CRDC receipt record.
- DASHI/Governance/BlackGirlsMatterExpulsionDenominatorExact.agda: zero observations, one-count hypotheticals and observed-ratio gate.
- DASHI/Governance/BlackGirlsMatterStudyScopeExact.agda: explicit sample, administrative-data versus testimony separation, disability/LEP omissions and negative controls.

**Current status:** Primary dataset identified; raw files, source SHA, denominator/indicator correspondence and arithmetic reproduction from original rows remain OPEN. Report-level arithmetic proof terms source-written only, not source-data reconstruction.

## Thirteenth pass — exact source-row and indicator-overlap interfaces (2026-11-09)

**Repository additions:**
- `DASHI/Governance/BlackGirlsMatterCRDCOriginalRowAdmissionExact.agda`: `VerifiedCRDCSource`, `MatchedOriginalCell`, `SamePopulationRateReceipt`, `ComparableRatePair`, `comparableRateCrossProducts`, `oneAndRepeatedSuspensionAreDifferent`, `printedEnrollmentTableCannotReplaceOriginal2011Enrollment`, `suppressedNotZero`, `missingNotZero`.
- `DASHI/Governance/BlackGirlsMatterCRDCAggregationBoundaryExact.agda`: `TwoIndicatorAggregation`, `disjointCountsRecoverUniqueStudents`, `sameTwoCategoryCountsCannotRecoverUniquePeople`, `differentCRDCMeasuresAreNotDefinitionalEqual`, `differentUnitsAreNotDefinitionalEqual`, `OriginalAggregationReceipt`.
- `CrenshawLegalAttributionCapstoneExact.agda` now imports original-row and aggregation owners; source-unit and suppression gates become part of the composite proof obligation.

**Crucial identification boundary:** Original 2011–12 CRDC separates students receiving one out-of-school suspension and more than one; the survey also gathers different discipline measurements for expulsions, law enforcement referrals and school-related arrests. Even when measure labels and race/gender cells match, the unit may be students counted once by indicator or disciplinary occurrences, and different measures may overlap the same student. Neither sums nor source-matched rates are admissible without correct unit and overlap/denominator receipts. See https://www.ed.gov/laws-and-policy/civil-rights-laws/civil-rights-data-collection-crdc-2021-22-school-year/2011-12-civil-rights-data-collection-questions-and-answers .

**Data-access audit:** The official ZIP URL was discovered through the historical-data landing page and independent archival record. The current container's direct DNS request to civilrightsdata.ed.gov failed; opening the ZIP through the web source also failed. Neither original row bytes nor digest nor denominator alignment has been obtained. Alternate archival 2011–12 CRDC mirror with detailed school-indicator files: https://www.datalumos.org/datalumos/project/219563/version/V1/view (historic federal data archived, not equivalent to having verified original federal ZIP). A mirrored file's institutional custodian and version must be recorded separately.

**Important remaining paid gate:** `source2011EnrollmentDenominatorSamePopulation` requires full independent census-year enrollment denominator and unit-consistent Black/white population by district. `blackGirlsMatterActual2011DisparityReplication` then requires actual school-aggregated original row sums and an explicit rule for indicator overlap. The formal modules deliberately supply no `VerifiedCRDCSource` instance, and no actual report-value replication is claimed.

**Attribution:** The CRDC source schema is a representation of OCR's official data collection; the 2015 report's narrative is Crenshaw with Ocen/Nanda; the constructive typed-source interfaces and counterexamples are DASHI. Source provenance does not imply report interpretation truth or real-world causal conclusions.

## Fourteenth pass — ratio identification and original archival source update (2026-11-10)

**Source-discovery improvement:** The U.S. Department of Education OCR still lists the downloadable 2011–12 CRDC; the archived DataLumos / ICPSR project offers **version V2 (2025-08-08)** with distinct school/LEA directories, a public-use match list, table layouts, definitions and data notes: https://www.datalumos.org/datalumos/project/219563/version/V2/view . The archival project is a source manifestation **distinct from** the DOE's native ZIP; its citation DOI `10.3886/E219563V2` denotes the archival project, not Crenshaw's publication and not the original federal file's SHA256. The archive explicitly says ICPSR has not reviewed/processed those deposited files. No bytes/rows were fetched or independently reconciled.

**New original DASHI formal owners:**
- `DASHI/Governance/BlackGirlsMatterDenominatorSensitivityExact.agda` — `publishedCountsUnchanged`, `denominatorsChangeRateDirection`, `caseCountsAloneDoNotDetermineRateOrder`, and exact numeral cross-products for two visibly synthetic enrollment scenarios. Holding the same Boston published Black/white girls' case counts (340/30), positive *hypothetical* denominators (3,400/3,000 vs 34,000/300) reverse the per-person rate ordering. The enrollment numbers ARE NOT actual district data, historical claims or probabilities based on verified OCR units. This counterexample is an information-limitation theorem only.
- `DASHI/Governance/BlackGirlsMatterSourceBoundRateOrderExact.agda` — `CertifiedBlackHigher` requires a same-year, same-district, same-race/sex, same-disability-eligibility, same-indicator verified OCR pair **plus** a strict cross-product inequality. `certifiedHigherRequiresSamePopulationRows`, `eligibilityMismatchCannotPayRate` and `publishedBostonCountsCannotChooseDirection` preserve the existing evidence boundary. No `CertifiedBlackHigher` for Boston or NYC has been constructed.
- `CrenshawLegalAttributionCapstoneExact.agda` imports both and exposes `publishedCasesCannotDetermineRateDirection` and `conditionalSameYearPopulationRateReceipt`.

**Exact conditional criterion:** For true unique-person numerators `b,w` and positive matched enrollment denominators `B,W`, a Black-girl rate greater than a white-girl rate is equivalent to `b*W > w*B`. Whether the 2015 report's "cases" are unique students is **not established**; a numeric cross-product made from the report's case counts alone does **not** prove rate ordering. Precise aggregation/overlap source evidence and report-method replication still required.

**Data-access failure:** Current container's HTTPS HEAD to the federal native 2011–12 ZIP failed at DNS lookup. Search-accessible official download page alone is not download or source authentication. The report PDF parsed text was accessible; a requested PDF screenshot returned a 19 MB source-size error. Do not claim PDF-page visual or cryptographic validation.

**Remaining narrow P0:** get native OCR or archived V2 file bytes and digest; inspect school + district/matchlist identifiers, disability eligibility, distinct discipline indicator definitions and suppression flags; reconstruct report-selected aggregate "cases"; recover same-year subgroup enrollment denominators with unique-person count semantics; reproduce count comparisons and rate ordering or document discrepancies. A working download is a hard external dependency, not a theorem generated by Agda.
