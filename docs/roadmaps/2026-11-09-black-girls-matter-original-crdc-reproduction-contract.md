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
