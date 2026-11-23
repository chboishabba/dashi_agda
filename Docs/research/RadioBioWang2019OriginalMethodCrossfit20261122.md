# P0-A2 — Wang 2019 original-method extraction, exact null, and Caltech raw-byte gate

**22 November 2026 (Australia/Brisbane).** **Current source status:** original published paper/methods and CaltechDATA file list inspected; **NO original human EEG bytes, MATLAB script contents, or extracted observed p-values were downloaded or rerun**. Local computation is **synthetic iid Gaussian sensitivity** with original study constraints, not clinical/physiological replication. **Owner:** continuation of [PR #1540 roadmap](../../Docs/roadmaps/RadioBioHumanAlphaBetaBioelectricFieldCrossDomainRoadmap20261122.md) and [P0-A original evidence audit](RadioBioHumanAlphaBetaOriginalEvidenceAudit20261122.md); original experiment/data remain solely attributed to Connie X. Wang, Isaac A. Hilburn, Daw-An Wu, Yuki Mizuhara, Christopher P. Cousté, Jacob N. H. Abrahams, Sam E. Bernstein, Ayumu Matani, Shinsuke Shimojo, Joseph L. Kirschvink. DOI **10.1523/ENEURO.0483-18.2019**, *eNeuro* 6(2), 2019. PubMed PMID 31028046 identifies the coauthor as **Jacob N. H. Abrahams**. Earlier repository editing erroneously substituted "Abrams"; this entry preserves the PubMed bibliographic spelling pending any original-version identity reconciliation.

Original source: [final article DOI](https://doi.org/10.1523/ENEURO.0483-18.2019), [CaltechAUTHORS original record](https://authors.library.caltech.edu/records/whbb7-57e98), [journal-version full text](https://pmc.ncbi.nlm.nih.gov/articles/PMC6494972/), [accepted-manuscript archived scan](https://upload.wikimedia.org/wikipedia/commons/0/02/ENEURO.0483-18.2019.full.pdf). The accepted-manuscript PDF was inspected by page and text in this audit. **Version-specific distinction:** the accepted manuscript's inclination denominator prose says **29 of 34** with no sham for 5, while indexed journal-final full text says **29 of 36**. Both share analysed inclination **N=29**. Treat the original-version denominator disagreement as an explicit publication-version reconciliation, *not* evidence of participant fabrication. The original journal-final table/Methods are required to determine the authentic final exclusion flow.

## Methods exact enough to constrain replication

The source methods, not our own intuition, require:

1. **Actual field stimulus:** 2-m Merritt coils in shielded chamber; Earth's field magnitude ~**35 µT**, directional rotation ~**100 ms**, intertrial interval **2–3 s**, active and counter-wound sham, pseudo-random SWEEP and FIXED; downward/upward inclination and distinct DecDn.CCW.N, DecDn.CW.N and DecDn.FIXED.N conditions. Original experiment recorded with **BioSemi ActiveTwo 64 scalp electrodes**, optically connected outside chamber. The stimulus is **not** an alpha-band RF carrier. Original EEG trigger/fluxgate alignment ±2 ms (512 samples/s).
2. **Artifact:** authors themselves measure induction artifact ~**10–40 µV** during the ~100 ms field rotation (depending on geometry/condition), including cantaloupe/dummy tests. Thus naive post-sweep EEG averaging without phase-locked component control is not the source-defined analysis. It must also be tested whether lasting, stimulus-correlated non-neural sensory cues survive sham.
3. **Epochs/time-frequency:** −0.75 to +1.25 or +2.25 s; baseline **−0.50 to −0.25 s**; 100 linearly spaced frequency bins **1–100 Hz**, Morlet wavelet convolution after EEGLAB extraction, and per-trial **log alpha-power** outliers rejected using **1.5×IQR** in the **6–14 Hz extended band**. Compute a *condition-specific ERP and subtract it from each condition trial* before induced/non-phase-locked power. Score electrode **Fz** relative to **CPz**; a 0.5 Hz Welch PSD is also provided as overall alpha evidence.
4. **Individualized time-frequency window:** average **6–14 Hz induced power over all conditions**, find the most negative post-stimulus time/frequency point between **0 and +1 or +2 s**, and construct a centered window **0.25 s × 5 Hz** (bounded by available spectrum). Use it to extract condition-specific **baseline-normalized dB alpha-ERD**. This is the critical selection step requiring sensitivity, not just a fixed 8–13 Hz bandpass.
5. **Unequal trial counts:** original algorithms use trial subsampling to match conditions, e.g. **100×32 FIXED** subsamples for 63 FIXED versus 32 CCW/32 CW; or **200×25** DN/UP subsamples for 50 FIXED, 50 DN, 50 UP. Without original RNG and full code, purported exact equality of the published F test is not certified.
6. **Independent group tests (not trial-level pseudoreplication):** inclination four conditions N=29; downward declination active three conditions N=26; reversal polarity six-cell DecDn+DecUp N=16. Sham declination N=18/26. Individual repeat measurements and 1000 permutations with FDR are separate from subject-level repeated-measures ANOVA.

## Analytic finding: selected minimum and the matched interaction are different statistics

The **source method** selects a time-frequency minimum of a pooled signal. A minimum can be negative under pure noise, independent of any experimental biology. For two independent centered Gaussian windows X,Y ~ N(0, sigma²):

    min(X,Y) = [X+Y-|X-Y|]/2,
    E[min(X,Y)] = -sigma/sqrt(pi).

The original paper's actual search has many **correlated** time-frequency windows rather than two iid points. The equation is **our mathematical illustration**, not the original authors' formula or observed data.

**Crucial safeguard:** a negative average after selecting a minimum does **not** automatically bias the subject-matched treatment interaction. In balanced exchangeable Gaussian null data (four conditions / 40 candidate windows) the 4-cell difference-in-differences contrast has zero expected value even if each marginal condition appears negative. A sensitivity experiment must test both overall marginal shift AND active–sham **interaction**, not treat any negative alpha map as automatic false positive evidence.

The original P0-A exact mathematical owner was extended with [window-selection source-matched null script](../../scripts/radiobio_wang_window_bias_sympy.py). **Local executed receipt:**

| Test / quantity | Actual result | Meaning |
| --- | --- | --- |
| SymPy two-window Gaussian minimum | exact **-1/sqrt(pi)** at sigma=1 | Mathematical selection bias |
| NumPy synthetic seeded 20261122; **4,000** experiments, **29** subjects each, **4** conditions, **40** independent candidate windows | PASS | One specified iid null, not source data |
| Mean pooled-window in-sample selected condition score | **-1.07949** (synthetic units) | Negative selected mean under null |
| Mean independent-heldout score at training-selected window | **+0.00033** | Selection optimism disappears under independent sample |
| Mean matched 4-cell interaction from selected training sample | **-0.00927** | Approximately zero by symmetry |
| Mean matched 4-cell interaction held out | **-0.00894** | Approximately zero by symmetry |
| Fraction p<0.05 in 29-person one-sample t-test of interaction, training vs held out | **0.0558 vs 0.0478** | Near nominal 5%, NOT evidence of inflated type I error for the interaction under THIS null |

These are **synthetic values**, not EEG power units, p-values from the 2019 study, or a significance test of human magnetoreception. A realistic next test should preserve wavelet covariance, serially-correlated trials, stimulus condition imbalances, subject-specific window estimates, nonstationarity, hardware pickup and the original authors' actual estimator/cluster correction.

## Actual external data attempts and fail-closed result

The authors' [CaltechDATA D1.930](https://data.caltech.edu/records/qyhmj-96g11) and [D1.931](https://data.caltech.edu/records/fx074-jee09) pages were source-read and expose **original MATLAB code and original .mat data** with catalogue MD5s. But direct file requests are redirected to **time-limited signed URLs at caltech2.osn.mghpcc.org**, inaccessible to the available web retrieval. A direct local request also failed DNS resolution to data.caltech.edu. Accordingly **zero original scripts or subjects obtained** and **zero locally verified source-file MD5 hashes**.

The new [Caltech original-file acquisition tool](../../scripts/radiobio_caltech_acquire.py) provides a fail-closed manifest, original DOI/record/file/MD5 identity, byte-stream download, locally computed MD5+SHA256, no-overwrite mismatch rejection, and optional one-subject sample. It is intended for execution in an **Internet-enabled environment**, not evidence that download occurred. The CLI plan/syntax check was executed locally (three script objects by default, five objects including two first .mat datasets), but the original-server fetch remains blocked. Original published content and licence must not be automatically committed or redistributed.

    python scripts/radiobio_caltech_acquire.py
    python scripts/radiobio_caltech_acquire.py --download
    python scripts/radiobio_caltech_acquire.py --one-subject --download
    python scripts/radiobio_wang_window_bias_sympy.py

**Admission gate for claiming actual W19 reproduction:** original bytes + MD5 verified → inspect authors' actual three MATLAB scripts and exact datatypes → recompute the original **29-person active/sham interaction** and **26-person CW/CCW/FIXED** with source-defined variable mapping, reject/time-frequency procedure, 18-person declination sham, plus matched 16-person polarity reversal → original-value comparison and genuinely independent held-out/window-control sensitivity. Neither the acquisition tool nor the synthetic simulation passes this gate.

## Further source-provenance distinctions

- First original source measurements, funding approval, 2018 deposited data, final March 2019 journal publication, 2022 Caltech platform migration, this repo's first source audit commit and exact local synthetic run are distinct timeline events.
- The original publisher's funding states **DARPA RadioBio D17AC00019 supported more recent analysis of the original study data**, not that the programme performed each measurement or proved intercellular RF communication.
- Null results in upward field rotations, fixed and sham trials belong alongside positive downward/CCW reports. A future independent replication may fail, succeed, or localize a narrower geometry-dependent effect; all count as genuine evidence.
- Do not promote any observed alpha-band EEG response to a beta-band result, external Schumann-mode entrainment, human illness, regeneration, or an alleged military programme without the source-to-recipient bridge.
