# P0-A4 — source-grounded trial-level held-out alpha audit harness

**Date:** 22 November 2026 (Brisbane); **parent:** [RadioBio P0 roadmap](../../Docs/roadmaps/RadioBioHumanAlphaBetaBioelectricFieldCrossDomainRoadmap20261122.md), [Wang original-method audit](RadioBioWang2019OriginalMethodCrossfit20261122.md), [heteroscedastic exact obstruction](RadioBioWangWindowHeteroscedasticExact20261122.md).

**Original attribution:** Connie X. Wang, Isaac A. Hilburn, Daw-An Wu, Yuki Mizuhara, Christopher P. Cousté, **Jacob N. H. Abrahams**, Sam E. Bernstein, Ayumu Matani, Shinsuke Shimojo and Joseph L. Kirschvink, *Transduction of the Geomagnetic Field as Evidenced from alpha-Band Activity in the Human Brain*, eNeuro 6(2), 2019, DOI [10.1523/ENEURO.0483-18.2019](https://doi.org/10.1523/ENEURO.0483-18.2019), [PubMed PMID 31028046](https://pubmed.ncbi.nlm.nih.gov/31028046/). The PubMed-author spelling **Abrahams** corrects an earlier erroneous substitution of "Abrams" in the prior audit. Original MATLAB methods and data belong to original authors, deposited by Kirschvink in [CaltechDATA D1.930](https://doi.org/10.22002/D1.930) and [D1.931](https://doi.org/10.22002/D1.931). **This harness is a DASHI independent follow-up, not an original-author analysis routine, not a republished original experiment and not a claim of EEG replication.**

## New completed producer

[Trial-matched crossfit analysis script](../../scripts/radiobio_wang_crossfit.py) accepts PRECOMPUTED per-trial **baseline-normalized time–frequency alpha-power** arrays via NumPy .npz with exactly these fields: power [trials, time, frequency], condition, subject_id, trial_id, times, frequencies. It intentionally does not pretend to read raw EEG, decode Caltech .mat structures, reproduce original EEGLAB artifact rejection/Morlet wavelet code, or implement the original source-defined condition-balanced ANOVA. Those gates must precede the true source replay.

The independent audit has these safety and identifiability properties:
1. **Subject identity preserved**; each participant is one eventual independent unit, regardless of number of stimulus trials. Subject/trial IDs are unique; incomplete matched cells explicitly reported **INCOMPLETE**.
2. **Split-before-select** on each person's trials **within each of four conditions** (active sweep, active fixed, sham sweep, sham fixed). No participant's test-half trials select the individual's window.
3. **Candidate mask** on 6–14 Hz and +0 to +1 sec by documented default. Select minimum of the all-four-condition **training** mean; calculate an independent post-selection window centered on that point with width 0.25 sec × 5 Hz. The precise source-specific individual search window must be verified after acquiring original MATLAB, including optional +2 sec stimulus cases.
4. **Interaction** (active sweep − active fixed) − (sham sweep − sham fixed) computed on training and heldout per subject, over the same selected window. There is no pooled trial-level p-value; the helper reports subject-level averages and retains per-split windows.
5. **Numerical guardrails:** reject duplicate IDs, impossible coordinates, nonfinite values, unknown conditions, or insufficient per-cell trials. Seed and subject/split identifiers determine stable split selection. Does not accept synthetic fixtures as real human measurements: without an independently hashed original Caltech .mat manifest, external preprocessed arrays are marked **UNVERIFIED_EXTERNAL_PREPROCESSED_NOT_ORIGINAL_RAW_EEG**.

### Local execution

An equivalent local working copy was executed in the container (NumPy installed) with the synthetic fixture: six pseudo-participants × four conditions × twelve trials; four heldout splits; six checks **PASS** for complete matching, deterministic repeat, missing-condition reject, duplicate trial reject and nonmonotone time axis reject. Example reported six complete subjects; average synthetic training interaction approximately −0.04328 and heldout approximately −0.04701. These **are arbitrary seeded Gaussian test numbers**, not empirical EEG amplitudes or study effect estimates. The GitHub-committed script has the same contract, with condensed source and result schema; no GitHub CI, EEG, kernel or experimental result is claimed. Run the **committed** script independently before treating it as validation of that exact repository blob.

Usage: python scripts/radiobio_wang_crossfit.py
After original bytes/metadata are verified and **original** EEGLAB preprocessing independently reproduced, explicit NPZ with all six fields can be used with --npz and --receipt. Keep human-derived data outside repository; store only nonidentifying aggregate and provenance-safe receipts if allowed by original licence.

### Authentic-data acquisition attempts on 22 November

[Original Caltech dataset 1](https://data.caltech.edu/records/qyhmj-96g11), [dataset 2](https://data.caltech.edu/records/fx074-jee09): the original pages are live and list the files and catalogue MD5s. All three original MATLAB download links redirect to short-lived signed object-store URLs at caltech2.osn.mghpcc.org; available web retriever returns a *non-accessible redirect*. Local container request to data.caltech.edu raises DNS resolution error. Broad searches for independently hosted unchanged MATLAB script copies returned no source-verified matched-hash mirror. **Zero original MATLAB bytes obtained and zero local MD5 confirmations**. No assertion of suppression or deliberate withholding follows from this infrastructure/transport restriction.

### Next empirical P0-A gate

A. Source-file acquisition from original CaltechDATA endpoint on Internet-enabled runtime; match published file MD5 and record licence/DOI/version.  
B. Exact original MATLAB scripts / .mat schema and authors' sequence (ERP removal, Morlet wavelet, trial-level artifact rejection, window choice, trial count matching), then original subject-level alpha-ERD results.  
C. Only afterward run the new independent heldout harness, and **condition-specific variance/covariance diagnostics** from P0-A3, on verified trial-level derived arrays.  
D. Preserve substantive negative controls: active fixed, sham sweep/fixed, CW, upward inclination, and instrument-only artifact tests where supported by the original source.  
E. Keep original-source analysis, derived crossfit result and independent new experimental measurements distinct in attribution and promotion level.

**Status:** source-listing and method review, one locally tested synthetic prototype, one committed independent analysis script. **Observed Wang 2019 effect not independently replicated.**
