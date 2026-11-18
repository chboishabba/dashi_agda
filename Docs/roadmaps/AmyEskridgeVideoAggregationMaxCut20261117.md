# Amy Eskridge video as evidence aggregator — maximum-cut execution (2026-11-17)

## PR and ownership

This PR is a **new video-source aggregator over existing producers**, not a new parallel scientific investigation. Entry point: `DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda`, imported from:

- `DASHI/Culture/AmyEskridgeEvidenceEverything.agda`
- `DASHI/Culture/MissingDeceasedScientificWorkEverything.agda`
- `DASHI/Culture/MissingDeceasedInvestigativeAttributionEverything.agda`

The transcript provided by the user is titled *She Researched Something THEY DON'T ALLOW. Then She Died* and ends at 32:44. **Original edited video identified:** Be Inspired / `@beinspiredchannel`, 12 May 2026 in channel indexes, `https://www.youtube.com/watch?v=acw16d6CCnY` (video ~32:47). The narrator's personal name, upload timezone and some original clip offsets are still unresolved; do not fabricate them. The 86 itemized claims are source-content paraphrases with timestamp pointers; they are not 86 independently verified findings or 86 source documents.

## 18 November 2026 — Aristotle search and actual Tukey HSD / pooled ANOVA implementation

**User-directed prior-art follow-up:** `Tukey` in `DASHI/Statistics/Vec15Robust.agda` only refers to **Tukey's IQR robust outlier fence**, not the post-hoc **Tukey HSD** family-wise error procedure. `Vec15Inference.anova15`, `tTest15` and `chiSquared15` are deterministic 15-vector scoring scaffolds; their `pValue` is a count, not a calibrated classical probability. Source consumers must not inadvertently treat them as inferential statistics.

**Actual original Aristotle proof-search prior art**:
- `DASHI/Reasoning/AristotleMergeExperimentDesignExact.agda`: visible observer collision, dependency/provenance experiment bundles, source-bearing `DiscriminatingLanguageExtension`, and an outcome-dependent sequential consumer plan.
- `DASHI/Reasoning/AristotleActiveExperimentalProofSearchLoopExact.agda`: proof-bearing active iterative loop with guarded compatible merges and selective reopening.
- `DASHI/Reasoning/AristotleActiveExperimentalProofSearchDynamicsExact.agda`: the actual `canonicalOneIterationCycle` and `canonicalClosurePath`, and possibility of consumer-relative early closure.
- `DASHI/Core/DiscriminatorSynthesisExact.agda`: original `extensionJoinSeparates` and nuisance-robust consumer separation.
We **import original values** rather than rebuild these search mechanisms. `AmyEskridgeBemAristotleExperimentalProofSearchWeldExact.agda` defines a *source-dependent next-step compiler*: absent raw XLSX bytes -> **acquire EXP1**; then reproduce the original published statistic -> reanalyse Transparent Psi per preregistration -> specify testable moderators and nuisance/variance conditions -> only then admit appropriate secondary Tukey comparisons. The original Aristotle search-cycle and closure-path proofs are linked directly. A synthetic final research state tests the decision logic; it is not a claim of obtaining raw Bem data.

### New actual classical-statistics implementations (reusable outside Bem)

| New native source | Exact computation | What is *not* certified |
|---|---|---|
| `DASHI/Statistics/OneWayANOVAPooledMSEExact.agda` | Three-group source summaries `(n,sum,sumSquares)`; exact within SSE: `sumSquares - sum²/n`, common-denominator pooling and residual df `N-3`; synthetic within-MSE=10, df=27 proofs | Normality, actual independent randomisation, group validity, source checksums, any original Bem one-sample t |
| `DASHI/Statistics/TukeyKramerPostHocExact.agda` | Unequal-sample Tukey–Kramer **q²** in integer cross-multiplied form with externally supplied alpha, k, df family-critical quantile; source guards, normality/common-variance/independence flags; synthetic reject/nonreject and missing-assumption refusals | Original studentized-range quantile proof, source authenticity, all-real normality, mixed-model/clustered analysis, post-hoc applicability without predeclared family |
| `DASHI/Statistics/TukeyKramerIntervalCalibrationExact.agda` | Conservatively compare integer/rational statistic with **lower/upper certified qcrit² bracket**: above upper -> reject, below lower -> fail, in between -> unresolved | Certified enclosing quantile by Agda alone; the user-supplied “calibrated” Boolean is a receipt claim and requires externally audited distribution-computation evidence |
| `DASHI/Culture/AmyEskridgeBemAristotleExperimentalProofSearchWeldExact.agda` | Source-stage gated next research discriminator and direct existing Aristotle cycle/closure-proof imports | Original datasets or actual experimental outcomes |

**Classical formula implemented**, for group samples `n_i,n_j`, sums `s_i,s_j`, and pooled `MSE = MSEnum/MSEden`:

```
D = abs(s_i*n_j - s_j*n_i)
q² = 2 * D² * MSEden / (MSEnum * n_i*n_j*(n_i+n_j))
reject only if q² exceeds a valid family-specific studentized-range critical q².
```

For *n* equal, this reduces to standard Tukey HSD; for unequal *n*, Tukey–Kramer. **It is post-hoc**, not the original primary Bem Experiment 1 one-sample null test, and blindly treating thousands of within-participant trials as independent groups is explicitly forbidden.

**Numerical acceptance actually executed locally:** SciPy `studentized_range.ppf(.95,3,27)=3.506426123354149`, squared **12.295024158540405**. On synthetic pooled `MSE=10`, three groups with `n=10`, means 10/16/11: exact `q²=36` rejects 10-v-16, `q²=1` does not reject 10-v-11. Unequal `n=6/12`, means 10/16: exact `q²=28.8` rejects. Source-level refusal of uncalibrated cutoff and non-independent units are represented as negative fixtures. An interval `[12.295, 12.296]` demonstrates a conservative decision with a borderline result remaining **unresolved**, but it was checked against SciPy *numerically*, not formally certified against the exact distribution (Agda proof of range inclusion still OPEN). The independent local script for this arithmetic passed; committed reusable checker `scripts/check_tukey_kramer_aristotle_bem_maxcut.py` implements the calculation plus source-owner checks. Original Agda kernel and committed checker have not been run against a locally checked-out repo, so do **not** report kernel green.

**Raw-data acquisition attempts:** Direct HTTPS request to `https://replicationindex.com/wp-content/uploads/2018/01/exp1.xlsx` failed in the container with DNS resolution error, and direct file downloader failed. **Google Drive/Sheets intentionally NOT touched**, per user's instruction to use them as a LAST RESORT only; there is currently no original XLSX in Google Drive established by user or source. No replacement/synthetic Bem dataset was imported or passed off as real.

**Priority outcome:** do NOT spend more research time implementing additional named classical stats without sourced experimental need. The ANOVA/Tukey infrastructure is now present as a **reusable conditional design operator**, but neither is the correct first test for Bem's Experiment 1. **P1a remains the original EXP1 XLSX acquisition and exact participant-level one-sample 50% analysis**, followed by predeclared 40+60 chronology tests; P1b Transparent Psi original mixed logistic/preregistration; P1c proponent 69-study meta-analysis and independently held-out moderator discrimination. The Aristotle active loop can adapt these next cuts based on results, and HSD/Tukey–Kramer is admitted only for a genuine predeclared multi-group post-hoc consumer.

---

## 18 November 2026 — native statistics + experimental-discriminator weld, actual author–critic chronology

### Existing prior art was much more relevant than generic scalar counterexamples

**Re-audited original code:** `DASHI/Core/DiscriminatorSynthesisExact.agda` supplies `CurrentObserverCollision`, `DiscriminatingLanguageExtension`, `ExperimentBundle`, `BundleSeparates`, `extensionJoinSeparates`, prospective consumer closure and nuisance-robust discrimination. `DASHI/Core/ExperimentalCoordinateDesignExact.agda`, `ActiveBidiDiscriminatorLoopExact.agda`, and `AnomalousTemporalProofSearchExperimentAdmissionExact.agda` already govern selective measurement, experimental intervention/admission and evidence-fibre refinement. We now use those **actual value-level original theorems** in `AmyEskridgeBemNativeStatisticsDiscriminatorWeldExact.agda`.

`DASHI/Statistics/Vec15Robust.agda` implements **Tukey IQR outlier fences**, Hampel MAD, winsorization and trimming on **15 natural-number prime-profile values**, **not Tukey HSD post-hoc pairwise inference** on arbitrary participant trials. `Vec15Inference.agda` and `PrimeProfileStatsSuite.agda` contain named ANOVA/t-test/chi-squared interfaces, but the current deterministic `pValue` field is `countNonZero15`, **not** a classical calibrated p-value. We import the real producer objects and retain their original domain; we cannot legitimately claim Bem statistical correctness by calling the similarly named scaffold. On actual data use SciPy/SymPy, hierarchical logistic models, participant-level t statistics, predeclared multiplicity and a trial-level source audit.

The new native discriminator builds **two explicitly counterfactual worlds** with the same published rate, then an independently authenticated historic-analysis-fork coordinate that separates them under the existing `Disc.extensionJoinSeparates` theorem. This is a **well-typed potential discriminator**, not a claim that a documentation fork has been discovered.

### New original-source evidence: Bem ↔ Schimmack correspondence, January 2018

**Primary participant correspondence as transcribed/hosted by Schimmack**, https://replicationindex.com/2018/01/20/bemcorrespondence/ (dated January 2018 exchanges; transcript not independently authenticated email-header bytes). This moves research beyond generic null-model conjecture:

- **10 January:** Bem states Experiments 5 and 6 draw from **100** negative/neutral-only sessions and an additional **150** negative/erotic/control sessions in 2002. He supplied a chronological CSV containing 250 sessions (the attachment bytes are **not yet inspected here**).
- **10 January:** Schimmack initially saw mismatched significant results in Experiment 6 when he used **paired comparisons with the neutral controls**; one paired test yielded t(149)=1.4057, two-sided p=.1619 and another t(149)=-1.3095, p=.1924, rather than published one-sample comparisons. **Crucial exculpatory control:** on **12 January he acknowledged that his test differed from Bem's published one-sample fixed-50%-null test** and Bem confirmed it. Do not call that methodological mismatch fabricated published statistics or an unresolved scientific discrepancy.
- **12 January:** Bem confirms **actual chronological Exp 6 interventions**: **91 sessions** with 16 negative/16 erotic/16 neutral; **19 sessions** with 12 negative/12 *stronger* erotic/24 neutral; **40 sessions** with 15 negative/15 stronger erotic/30 neutral. This is genuine documented within-experiment protocol change and therefore a valuable time/heterogeneity variable, **not proof that any specific change caused a positive result**.
- **15 January:** Bem's own chronological table splits **Experiment 1 into 40 + 60** sessions in 2006; do not assume 100 identical session conditions without checking original source. Experiment 1 chronology and Experiment 6 interventions **must not be merged as the same treatment change**.

The exact correspondences and 40+60, 91+19+40 finite totals are in `AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact.agda`, with a negative control for the retracted accusation based on the wrong paired test. Historical person-specific alleged misconduct remains unproved.

### Raw-data availability and the genuinely strong 69-study steelman (new original-source acquisition)

A previously missed **20 January 2018 original public data release** is directly linked on the primary correspondence page:
https://replicationindex.com/2018/01/20/bemcorrespondence/

Schimmack's article says Bem authorised him to distribute all nine study datafiles, and includes individual original workbook links **EXP1 through EXP9**; exact first and sixth:
- **Original Experiment 1** https://replicationindex.com/wp-content/uploads/2018/01/exp1.xlsx
- **Original Experiment 6** https://replicationindex.com/wp-content/uploads/2018/01/exp6.xlsx

**Status changed:** These workbooks are *located public primary data*, not inaccessible research records. The current model runtime's web reader identified the attachment URLs but rejected the binary XLSX response, and the isolated local container cannot resolve the host. Accordingly, the original workbook **contents have not been inspected or reproduced**. No analysis based on guessed contents is permissible. Source identity and permission are encoded in `AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact.agda`, and acquisition is the **immediate P1a gate**. User or a network-capable checkout can download the precise source bytes. When retrieved, preserve original XLSX, checksums and the recorded header/participant/session coverage; separately decode via the data pipeline and reproduce the exact one-sample fixed-50%-null t tests **before** contrasting with the critic's paired-control alternative.

The **25 January 2018 author reply** is an especially important steelman: Bem claims the 90-study meta-analysis separately evaluated **69 independent studies** (33 laboratories, 14 countries), including **31 exact computer-program replications** and **38 modified replications**; he reports **z=4.16, p=1.2×10^-5, Bayes factor 3.85** for the independent subset. The public reply also denies result-based study discard and explains changes to earlier pilot procedures. These are attributable *original author statements*, **not independently replicated calculations or proof of no bias**. A serious adjudication must reproduce the 69-study subset and quality/selection, not dismiss the steelman simply by excluding the original Bem papers. The RCT/consensus 2023 null is strong *for its specific target design* but does not algebraically contradict a heterogeneous meta-analytic positive value without matching experimental protocols/strata.

`AmyEskridgeBemOriginalProtocolCorrespondenceWeldExact.agda` now carries the exact workbook locators and the 31+38=69 source-count witness (the latter proves only the arithmetic of the published assertion). This is a higher-yield source cut than more toy family-wise rates.

### Additional exact-statistical control that changes the interpretation

The original paper reports **eight of nine experiments significant**, not merely *at least one of nine*. Under the **strictly hypothetical** model of nine independent, preregistered, calibrated alpha=.05 tests all under the null,

- P(**at least one**) = 1 - .95^9 = **0.36975059**, an ordinary multiple-testing illustration.
- P(**at least eight**) = 9(.05)^8(.95) + (.05)^9 = **3.359375 × 10^-10**.

**Neither number is a valid probability of Bem's actual publication event without the experiment dependence, selection/search universe, directionality, reporting and source provenance.** In particular the toy “at least one” number is *not* an explanation for eight positive original papers. The reanalysis must test effective analysis count, original chronological stopping, internal protocol evolution, study-specific participant structure and independent source replications, with competing effect model preserved.

Two **synthetic** 2×2 contingency tables with 828/1560 total successes but different subgroup patterns (430+398 versus 414+414 successes, each across two 780-trial groups) demonstrate exactly why marginal success rate cannot identify a historical moderator. They are **not fabricated Bem observations**.

### Source-count correction and data acquisitions

The Transparent Psi 2023 original paper has an **internal inconsistency**: its study-design discussion says Bem had **1650** erotic trials, but the same paper's results comparison explicitly says **1560** erotic trials; the 2025 PLOS ONE paper also says 828/1560. Retain the conflict in the source registry and independently inspect the complete original Bem 2011 Table/experiment text and session-level data before promoting the numerator. **The distinction doesn't materially change its null-replication finding, but it matters for exact test reconstruction.**

Original data leads:
- Transparent Psi raw consolidated `final_combined_live_data_for_analysis.csv`: **https://osf.io/24qkr**; born-open recordings: https://github.com/kekecsz/transparent-psi-results/tree/master/live_data . Original paper confirms **2115 participants / 37836 erotic trials**, 25 incomplete sessions, 192 absent trials; 3 additional sessions truncated at preregistered stopping threshold. Mixed-logistic clustered Wald 99.75% CI **49.11–50.67%**; 3 Bayes factors plus one mixed logistic simultaneously triggered preregistered stopping at the first analysis boundary.
- Bem original 2011 Experiment 1 and 6 data files are now **located as linked original XLSX attachments**, but bytes were **not retrievable in this execution environment**; original session-level reproductions remain open. The 2018 correspondence also reports Bem sharing 250 chronological CSV sessions for Experiments 5/6, but its precise original bytes remain uninspected. The contemporaneous data provenance should not be replaced with data reconstructed from narrative.
- Unpaid: direct 2011 data and scripts; original blinded RNG/session controls; precise participant/trial strata; original author preregistration/analysis chronology; independently audited moderation test with held-out predictions.

**Acceptance:** the existing `scripts/check_amy_eskridge_bem_steelman_realistic_sympy.py` now checks the genuine DASHI discriminator/Tukey/ANOVA source identity, exact 8-of-9 conditional probability and synthetic nonidentifiability as well as the original literature/protocol correction. Repo source-blob checks may be run without CI; full Agda kernel and full checker in a local checkout remain separate.

**Priority now:** **P1a** original Bem Experiment 1 records and independent author-admitted protocol strata; **P1b** Transparent Psi raw participant-data/analysis replay; **P1c** rigorous moderator-v-null preregistered comparison using native discriminator/coordinate contracts. Do not spend another round on generic statistical constructors, simulation-only work or p-hack accusations.

---

## 18 November 2026 — Bem Experiment 1 steelman-versus-realistic identification audit

**Task:** preserve Bem's strongest admissible hypothesis and the most realistic null/selection explanations; mathematically prove the attainable consequences of each and discriminate them with exact original evidence. **DO NOT assert that Bem "must have p-hacked", selectively published, violated the protocol or fabricated results.** A scalar reported percentage cannot logically identify which causal/statistical mechanism generated it. The null model with genuine nonzero sampling probability is a counterexample to the universal "must have suffered analytical malpractice" conclusion.

### Required analysis and formal proof gates

| Gate | Position and proper evidence scope | Status |
|---|---|---|
| **B0 — exact primary-source calibration** | Bem *Feeling the Future* (JPSP **2011**, DOI **10.1037/a0021524**) Experiment 1's **53.07% and 1,560 erotic trials** as *reported* by the original 2023 replication. Do **not** silently manufacture a hit count from a rounded percentage or conflate the 100-person t-test with independent trials. Original full manuscript: https://dbem.org/wp-content/uploads/2023/02/FeelingFuture.pdf | Primary paper/source identity located; raw participant analysis **OPEN** |
| **B1 — mathematical identifiability** | Construct null random-fluctuation, prospective stable effect, analytic-choice and protocol-moderator explanation models returning the **same reported scalar**. A single scalar alone cannot prove that any one latent mechanism occurred. Agda `AmyEskridgeBemSteelmanRealisticIdentifiabilityExact.agda` provides finite same-observation and non-coercion witnesses. | **Formally encoded, kernel verification OPEN** |
| **B2 — exact sampling probability** | Conditional on *iid unbiased Bernoulli trials*, any specified 1,560-bit record has probability **2^-1560 > 0**. For a *proxy count* of at least 828 successes, evaluate the exact binomial tail; distinguish this conditional binomial from the manuscript's session-level (t) statistic and the paper's reported percentage (which must not be converted to exact hit counts). | Exact script committed, full repo run **OPEN** |
| **B3 — multipath selection sensitivity** | For **m independent** predeclared null tests and false-positive rate alpha, prove (1-(1-\alpha)^m) and calculate 9-test illustrative envelopes at alpha=.01/.05. Then generalise to **dependence** and actual original analysis choices; *nothing permits treating Bem's nine experiments as nine iid tests by default*. Selection creates risk, not proof of historic selection. | Conditional mathematical identity included; actual effective test family and source decisions **OPEN** |
| **B4 — strongest steelman** | Bem's 2011 mechanisms and **2015 publication / January 2016 v2 90-experiment meta-analysis** (DOI 10.12688/f1000research.7177.2) count as *reported positive original literature*. Formalize how replication effects might be moderated by erotic-image set, recruitment, reward, belief/sensation seeking, site and preregistration. Demand a **predated, signed interaction and out-of-sample held-out replication** before any moderator can explain the observed source change. | Steelman evidence mapped; preregistered interaction **OPEN** |
| **B5 — strongest realistic alternative** | Compare trial- versus participant-level aggregation; optional stopping, exclusions, order of tests, transformations, demographic moderators, site and target-side controls, missingness, reuse of analyzed materials, provenance of randomisation; exact protocol **diff**, not speculative accusations. Original 2023 study had **2,115 valid participants**, **37,836 erotic trials**, **49.89%** and **99.75% mixed-logistic CI [49.11%, 50.67%]**. Compare as an interval, not direct proof of any 2011 p-hacking. | Bounded variables enumerated; 2011 raw records/protocol replay **OPEN** |
| **B6 — adversarial data reanalysis** | Acquire Bem's participant/session-level original data, code, raw event order, RNG metadata/seed if available, dated protocols, exclusions, manuscripts/analysis chronology; acquire 2023 public `final_combined_live_data_for_analysis.csv` from the paper's OSF/author GitHub plus preregistration, test accounts excluded and script. Reproduce **published statistics** first, then compare against predeclared alternatives with multiplicity-correct uncertainty, source attribution, direct-vs-proxy model gates. | **OPEN** |
| **B7 — decision** | Prefer no effect for **that protocol's above-chance guessing** when consensus replication falsifies original effect size; retain alternative fully specified psychophysiology paradigms and weaker subpopulation possibilities as distinct obligations. Historical bias/selection may be promoted only if **independent contemporaneous records** demonstrate it; a finite null-compatible report cannot pay such a claim. | Experimental nonreplication **PAID in source**, historical cause **OPEN** |

**New sources**:
- Original 2023 Transparent Psi collaborative replication, https://pmc.ncbi.nlm.nih.gov/articles/PMC9890107/, DOI **10.1098/rsos.191375**: 49.89%, 2,115 individuals, 37,836 erotic trials; 99.75% **mixed model** CI [49.11%, 50.67%]; original effect 53.07%. Panel co-designed with both proponents and sceptics; deviations (different pictures, compensation, multi-participant testing) acknowledged; not claimed automatically irrelevant by this roadmap.
- Original Bem et al. **2015** 90-experiment proponent meta-analysis, DOI **10.12688/f1000research.7177.2**: **steelman**, not independent dispositive validation; investigate heterogeneity, lab pedigree, selection and publication, and quality-sensitive robustness.
- `DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact`, pre-existing `bemInitial2011` and `transparentPsi2025`, remain evidence-trajectory owner; no new psi ontology is needed.

**Execution:** `DASHI/Culture/AmyEskridgeBemSteelmanRealisticIdentifiabilityExact.agda` and `scripts/check_amy_eskridge_bem_steelman_realistic_sympy.py` added on the **existing** PR #1528. SymPy exact conditional calculation can be run with `python scripts/check_amy_eskridge_bem_steelman_realistic_sympy.py`. Do not claim Agda 2.9 kernel or raw source rerun unless they are actually executed. When original data are obtained, run the actual preregistration/exclusion/participant aggregation audit and separately test the strongest frozen moderator alternative.

### Revised priority across original programme

1. **P0 — protect original H2/H3 exact-object and causal evidence obligations** (R68–R88 scientific work/custody): only update on new identity-bearing original records; this remains the *most consequential* video-scientists claim, but repeated unproductive bounded searches are **not** high yield.
2. **P1 — Bem original-vs-Transparent-Psi B0/B6 + B4/B5 data replay** is now the **highest experimentally tractable next video action** with open public 2023 raw data and a well-defined published endpoint. It is not a new claim that Bem is already convicted of malpractice. Stop once methodological explanations are source-limited or once acquisition of 2011 originals is exhausted.
3. **P2 — original missing 18:39 voice/footage and physiological presentiment**: clarify attribution, then run *different* protocol-family preregistered tests if actually justified by independent anomalies.
4. **P3 — Looking Glass / 2016–17 equipment prediction, EU/UN/NATO custody**: source interview done; **yield** until a dated and authenticated predeclared event, device, receipt, inventory or independent prediction appears. Otherwise no statistical score or physical-operational proof is possible.
5. **P4 — narrower historical and experimental items** (Li AMCOM records, Poher NASA test identifier, false historical patent/legislation assertions) re-open only on genuine new original source; existing producer work is retained.

**Interpretation:** **strongly rejecting a Bem-sized effect in a well-powered specific protocol does not prove what caused a positive historic result.** Conditional chance/selection mathematics is proved separately from the empirical history of research conduct. Do not claim the original result *must* have contained a flaw merely because Transparent Psi disagreed.

---

## 18 November 2026 — late-video claim 064–085 implementation: exact original/source/experimental cut

### One original interview does not give twenty-two independent witnesses

The late section of the 2026 Be Inspired 32:44 transcript (edited **16:02–32:04**) now has all **22** claim objects individually welded to actual source-role owners in `DASHI/Culture/AmyEskridgeVideoLateSectionEvidenceBidiExact.agda`. This **reuses** `AmyEskridgeVideoOriginalClipLineageExact`, `AmyEskridgeVideoClaimProducerWeldExact`, the pre-existing governance anomaly temporal fibre, experimental-admission framework, and the pre-existing Mandela-memory scientific producer.

| Claim IDs | Family | What we can now say | What CANNOT be inferred |
|---|---|---|---|
| 064–065, 069, 071–074, 076–077, 079–080, 082–085 (15) | Burisch first-person original June-2007 interview clips, with exact/family source location | Dated speaker assertion and its editing relationship to the supplied video | Actual Looking Glass, multiple timelines, wormhole operation, NATO/EU/UN custody, facility history |
| 066–067 (2) | Philip K. Dick 1977 Metz speech and Deutsch 1995 Noorderlicht interview | Original philosophical/scholarly quotation provenance | Quantum-mechanical proof of historical changes or technical operation |
| 068, 075, 078, 081 (4) | Be Inspired original 2026 narrator synthesis | The narrator said/inferred it; the original upload is identifiable | Underlying independent confirmation, genuine calibrated forecast, geophysical portal or government anomaly mapping |
| 070 (1) | Narrator's Bem 2011 attribution and **unidentified** physiological-clip audio | Distinct psychology and physiological literature, explicit original-video source gap | A Bem 2011 *physiological* experiment, general ESP proof or actual time-machine source |

The core `AmyEskridgeVideoClaimProducerWeldExact.agda` itself was repaired so **066, 067 are no longer marked unlocated**; narrator-only claims 068/075/078/081 explicitly reference `Source.videoTranscript` rather than fictional missing third-party footage. 070 now carries both the authentic Bem publication and the still-unidentified clip-09 source lead. Original 2007 Burisch statements use exact relevant 2007 clip-family objects; a speaker's claims are not independently observed hardware.

One source-role correction changes the temporal interpretation of **claim 084**: the sentence “not being used right now” refers to **June 2007**, NOT November 2026. Do not convert it into current operations or a universal lifetime shutdown.

### Conditional prediction max-cut (published 2007, referring to ~2016–17)

**Original primary transcript:** Dan Burisch / Kerry Cassidy, *Stargate Secrets*, Project Camelot, Las Vegas **June 2007**, part-1 text:
https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html

The exact exchange around lines 635–667 has Burisch saying that he *expects/probably* the allegedly separated equipment might be reassembled *about 2016–2017*, followed by an unverified EU/UN/NATO tri-custody claim. This is a source-backed **dated conditional expectation**, not a scored operational forecast. Critically, no frozen explicit probability, unambiguous observable target, independently authenticated event/outcome or predeclared verification/scoring rule accompanies that claim. Mere passage of 2017 is NOT a verified failure or success.

`AmyEskridgeVideoTemporalForecastAndPsiMaxCutExact.agda` now contains:
- Exact `ForecastProvenance` holding source clip, publication year, forecast interval, `Maybe Nat` frozen probability and original event/outcome gates; published **2007 <= 2016–17** proof.
- Admission `isScorable` requiring **bounded frozen probability (0–1000), fixed event definition, and an independently authenticated outcome**, so Burisch's actual item yields `notScorable` and `applyFrozenBrier ... ≡ nothing`.
- A genuinely mathematical **finite Brier score** with proper integer exact arithmetic; three explicitly **synthetic** 0.9/0.5 fixture checks (0.01/0.81/0.25 squared error), plus one admitted synthetic forecast. None is presented as an original Looking Glass reading.
- Invalid producer coercions (dated interview -> operating device; shared false memory -> altered history; CIA STARGATE remote-viewing files -> alleged mechanical Stargate) explicitly prohibited.

### Already-existing predictive / physiological formalism reused — not reinvented

Before this PR, `DASHI.Governance.AnomalousPhenomenonTemporalEvidenceTrajectoriesExact` had typed distinct `bemPrecognition` (2011/2025), `presentimentPhysiology` (2012/2018), and `stargateRemoteViewing` (CIA experimental / 1995 operational review). `AnomalousTemporalProofSearchExperimentAdmissionExact.presentimentRoute` already admits a preregistered, fixed-stopping/scoring physiological experiment; the remote-viewing historical-source route is blocked as proof of operational utility. `IbrahimSnowballMandelaReligionIndigenousMemoryBraidingBidiExact.prasadBainbridgeMandelaSource` already owns the 2022 peer-reviewed visual memory controls (DOI 10.1177/09567976221108944).

The video-specific adapter **imports those exact original objects**, not a new generic hypothesis engine; no direct same-object edge is permitted between the CIA remote-viewing programme called STARGATE and Burisch's unverified claim of mechanical gates.

**New inspected primary studies, with explicit protocol differences:**
- Bem, JPSP **2011**, DOI 10.1037/a0021524: nine cognitive/affective experiments, **not** the exact physiology demonstration at 18:39.
- Kekecs et al., Royal Society Open Science **2023**, DOI **10.1098/rsos.191375** (correct original article identifier): adversarial consensus multicentre replication of Bem's Experiment 1, **10 laboratories, 2,115 valid people, 49.89%** successful choices, original Bem **53.07%**, random chance 50%. Published finding: did not replicate Bem's original effect. DOI and number sourced to https://pmc.ncbi.nlm.nih.gov/articles/PMC9890107/.
- Walleczek et al., PLOS ONE **2025**, DOI **10.1371/journal.pone.0335330**: their **Study 2** reported a significant **below-chance** erotic-trial result **49.65%, p=0.013**, a positive finding only in the paper's own *anomalous lower-than-chance* interpretation. Larger **Study 3** produced **50.07%, p=0.496, N=217,800 erotic trials**, failing to reproduce Study 2. **This does not count as 217,800 independent participants**. https://journals.plos.org/plosone/article?id=10.1371/journal.pone.0335330.
- Mossbridge/Tressoldi/Utts **2012** DOI 10.3389/fpsyg.2012.00390, and Duggan/Tressoldi **2018** DOI 10.12688/f1000research.14330.2, are *pre-stimulus physiology* meta-analysis families; they remain contested and scientifically distinct. Original physiology speaker/footage at **18:39** unlocated.
- The original Mandela-effect control (Prasad/Bainbridge **2022** DOI 10.1177/09567976221108944) directly investigates confident shared visual errors; it does NOT prove either changed history or the universal falsehood of recollection.

### Tests and acceptance

Committed new source-driven checker `scripts/check_amy_eskridge_video_late_maxcut_sympy.py`; same-turn GitHub-blob structural check **PASS 15/15 source/coverage/producer conditions** (86 baseline retained, exactly 22 late claims, 16 source clips, corrected Dick/Deutsch/Bem source roles, 2007 time bounds, pre-existing governance source owners, correct DOI strings, no unintended duplicate `originalPaper` constructors). Independently executed exact Python/SymPy arithmetic for 2011/2023/2025 reported rates and the synthetic Brier fixtures (**PASS**), with no invented real event record. `AmyEskridgeVideoTypedObligationWeldExact` gates 066/067/068/070/072/075/084/085 now have specific unpaid context/replication/future-prediction/custody obligations, rather than generic apparatus checks.

The **full committed script was NOT run against a local repository checkout** because this runtime has no network access to GitHub; the original Agda kernel admission was also **not run** (Agda executable unavailable). Do not substitute source parsing or model-side `refl` text for a typechecked proof.

Reproduce in repository:

```bash
python scripts/check_amy_eskridge_video_claim_weld_sympy.py
python scripts/check_amy_eskridge_video_late_maxcut_sympy.py
DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda
```

**Next high-alpha frontier is narrowed to exact receipts**, not additional speculative ontology:
1. Locate/authenticate the actual **18:39 physiological speaker and original edited footage**; keep Bem 2011 and physiological studies separate in the consumer.
2. Acquire preregistered physiological experiment data/protocol or independently audit a recent full high-rigour source dataset; report robustness, leakage, baseline time locking and optional stopping, distinguishing from cognitive guessing.
3. Identify a **predated, publicly inspectable Looking Glass forecast with fixed outcome and independently authenticated observed result**, or an identifiable machine/document record. Without those, neither Brier score nor a physical mechanism test is admitted.
4. Locate exact **EU/UN/NATO component inventory/serial/custody record**, if it exists; otherwise keep speaker testimony as a source object only, not an accusation or absence finding.
5. For Frenchman Mountain, specify and measure a physically discriminating traversability effect beyond conventional magnetic/gravity/geological anomalies; the speaker's label is not evidence.
6. Run Agda/kernel and full committed script, resolve source-level errors if any. Continue the previously developed cohort H2/H3 lanes **only** when exact new original material advances the already specified 88-round promotion gates.

---

## Prior-art correction: TWO distinct eleven-person rosters and eighty-eight rounds

**Re-audit 18 Nov 2026:** The repo has considerably more work on eleven scientists than this video PR originally acknowledged. Original source-of-truth modules:

1. `MissingDeceasedTwentyScientistRoundRobinProgressExact.agda` fixes `usScientificCohortCount = 11`, `chineseScientificCohortCount = 9`, and lists `twentyScientistRoundProgress` in exact source order. The **U.S. research 11** are Loureiro, LeBlanc, Maiwald, Monica Jacinto/Reza, Grillmair, Hicks, McCasland, Anthony Chavez (name/technical-identity still split), Jason Thomas, Amy Eskridge, and Ning Li. The cohort label reflects a research collection, not a forensic determination that all 11 had the same fate or technical role.
2. `AmyEskridgeVideoEleventhMediaRosterWeldExact.agda` contains a source-entitled **Fox April 17 2026 media eleven**: Loureiro, Maiwald, Monica Reza, Grillmair, Hicks, McCasland, Anthony Chavez, Jason Thomas, Amy Eskridge, Melissa Casias, Steven Garcia. 9 name-level overlaps, 2 U.S.-research-only (LeBlanc, Ning), 2 Fox-only (Casias, Garcia). **The 13-name union is a name-key count, not an authenticated thirteen-person causal cluster.**
3. `MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact.agda` contains **House-context 10** (8 shared with research US11 + Casias and Garcia), while the actual 20 Apr 2026 House letter raises concern about **at least 10 unconfirmed reported cases** beginning in 2023. **The House did not enumerate all ten by individual name; R44 uses additional reporting to make the reconciliation.**
4. `MissingDeceasedRosterRoleAndCommitteeWeldAuditExact.agda` and `MissingDeceasedIdentityAttributionAuditExact.agda` already block promotion of Casias (administrative role) and Garcia (property custodian) into scientists, and block automatic identification of missing Anthony Chavez with published engineer Mark Anthony Chavez.
5. `MissingDeceasedTwentyScientistRoundRobinEverything.agda` is a scientific-work/technique aggregate for early rounds and generic operator/proof implementations. **`MissingDeceasedCommonObjectProgrammeEverything.agda` is the separate, genuinely later aggregator covering object/custody/evidence/provenance work through R88.** `MissingDeceasedScientificWorkEverything.agda` and `MissingDeceasedScientificWorkCustodyEverything.agda` contain the main long-lived scientific and event-time/custody graph. The video must consume these existing owners, NOT rebuild the twenty-cohort research.
6. `MissingDeceasedTwentyScientistRound50ProfessionalEvidenceRoomExact.agda`, R51 SensibLaw/PNF, and R49 source-origin independence already supply primary-carrier authentication, proposition stage, origin-group independence, source role, evidence reliability/polarity, lawful preservation, professional publication and hypothesis discrimination. The video's typed 86-claim gates are **thin video-local projections**, not the investigation's first provenance theory.

**Typed reconciliation added here:** `AmyEskridgeVideoUS11PriorArtReconciliationExact.agda`. Directly imports the R1 scientific records, Fox 11 media records, R44 committee records, non-scientist controls and latest exact-object/FOIA owners. Includes definitional proofs of 11 US + 9 Chinese = original 20, both lists of 11, nine named overlaps, two research-only names, two media-only names, 13 union name keys, plus exact original-source statements about funded POAMS, work-specific HCB, LeBlanc WBS and Ning Army FOIA status. No string similarity or media-list membership serves as same-person or causal evidence.

### Existing high-alpha results that MUST NOT be re-opened as missing base constructors

| Existing owner | Already paid before video | Remaining exact leaf / yield policy |
|---|---|---|
| R31–R39, R68, R69, R70 (Reza/McCasland HCB) | Monica-to-Mondaloy/HCB role; McCasland programme-level reference; AIAA retrospective **DOI 10.2514/6.2020-3833** documenting Mondaloy within HCB; named task managers other than McCasland | Contemporaneous **same HCB task/review/approval** bearing McCasland's own identity. R70 bounded search had no hit; **branch may yield until new identity-bearing lead** |
| R28–R30, R72–R79 (Amy NASA POAMS) | NASA TM **20205010911**; active SAA `SAA8-1519855` and separate **POAMS Familiarization `SAA8-1519855.1`**; Quantum Machines LLC counterparty, Chris Milam named requester/funder | Signed SAA subagreement/attachment, STI/IP/release record or NASA transfer document **specifically identifying Amy/Institute**. R79 bounded negative search; do not infer hiding or suppression |
| R80–R83 (Joshua LeBlanc) | Named exact NASA Fission Surface Power WBS **658133.04.01.22.01.06** and neighbouring project records | Second retained person on that exact WBS, qualified device/data/succession evidence; R83 says only LeBlanc found in declared searched scope, not proof of universal non-participation |
| R71, R84–R88 (Ning Li) | Original DoD FY2001 archive locator `DAAH01-01-9-R001`; Texas 2005/2006 identifier occurrences; OSD/JS FOIA `23-F-0043` **administrative closure after non-narrowing**; DoD OIG FOIA **DODOIG-2022-001077** request log; scoped FBI/OSD/OIG/Army producer routes | **Do not interpret administrative closure as “no records”.** Inspect original DoD annual-report bytes/page 66, get Army AMCOM instrument/SOW/payment/closeout and exact test result. R88 locates an AMCOM primary-document request route; public-source recrawls are now lower alpha |
| R40–R52 + original scientific modules for all 20 | 20 retained technical research kernels, exact grants, papers, patents, event-time constraints; H2 and H3 hypothesis-discrimination framework | An **identity-bearing cross-person exact-object weld (H2)** and **separate operational targeting/cause proof (H3)** remain absent. Technical topic overlap, inquiry and unusual death do not pay either |

**Prior-art acceptance boundary:** a source or module stating `true` means that exact recorded proposition is encoded as paid **within that source owner's bounded evidence policy**, not that external scientific or forensic facts have been independently re-proven in the video PR. Other status records remain open. The priority is **reuse + specific original-record acquisition**, not additional generic provenance constructors, retrospective Fox clustering or reciting unchanged web articles.

---

## Existing owner graph (located in repo)

| Owner | Authority retained | Video join |
|---|---|---|
| `MissingDeceasedTwentyScientistRound44OfficialInquiryCohortExact` | Reconstructed ten-person public reporting cohort: eight in analytical twenty, two outside | 00:21 and suppression-pattern claims are compared, not equated |
| `MissingDeceasedTwentyScientistRound11SourceReplayParetoExact` | **Round 11** of scientific-work progress on **twenty** people, not a special eleven-person list | No authority transfer from iteration number to roster count |
| `MissingDeceasedRosterScopeReconciliationExact` | House/expanded UAP/historical technical/China comparison are distinct denominators | Eleven must have named member-and-scope receipts |
| `MissingDeceasedRosterRoleAndCommitteeWeldAuditExact` | Some named people are administrative/asset-custody rather than scientists; event status differs | Reject all-eleven-are-scientists inference |
| `MissingDeceasedIdentityAttributionAuditExact` | Role/technical identity gates; Anthony Chavez vs Mark Anthony Chavez not welded | Reject shared technical-programme assertion without identity |
| `AmyEskridgeHAL5AntigravitySourceEntitlementExact` | HAL5-hosted 6 Dec 2018 historical talk, source-entitled discussion | 03:02 and bounded references |
| `AmyEskridgeHAL5PrimaryLiteratureSnowballExact` | Li/Torr (1991/1992), Podkletnov/Nieminen (1992), Woodward (1992) with source inspection scope | Physics *abstract* claims at 09:30, 10:43, 12:01 only |
| `AmyEskridgeDemiseCircumstancesSnowballExact` | Amy's 11 June 2022 family-obituary date, separately reported manner and unlocated autopsy/police | Video 2022 death year without explaining cause |
| `MissingDeceasedInvestigativeAttributedSourceAtlasExact` | NASA NCC8-124 and Li 1997 static test, dated original programme and reported null/constraint | NASA/Li claims cannot convert to Army success or suppression |
| `MissingDeceasedAttachmentSourcePromotionLedgerExact` | Previous *different* 71-page attachment's source-promotion gates | Never assume same claim is supported by that unrelated attachment |

### Exact House-ten reconstructed cohort (not the video's self-proven list)

Michael David Hicks; Monica Jacinto / Monica Reza; William Neil McCasland; Frank W. Maiwald; Carl J. Grillmair; Nuno F. G. Loureiro; Anthony Chavez; Jason R. Thomas; Melissa Casias; Steven Abel Garcia.

**Source**: House Oversight and Government Reform, *Comer & Burlison Seek Information on Missing Nuclear and Rocket Scientists*, 20 April 2026, https://oversight.house.gov/release/comer-burlison-seek-information-on-missing-nuclear-and-rocket-scientists/ and original FBI letter https://oversight.house.gov/wp-content/uploads/2026/04/FBI-Missing-Scientists-Letter_4.20.26.pdf. The **primary committee text expressly calls the underlying reports unconfirmed**, alleges **at least ten**, and describes the sequence as beginning in **2023** with Hicks. It specifically names Hicks, Reza and McCasland, while the repo's other seven names are resolved through downstream reporting/context, **not** falsely attributed as explicitly enumerated in the letter.

Amy's family-obituary date is **2022-06-11** according to `AmyEskridgeDemiseCircumstancesSnowballExact`, so it is impossible to quietly count her as part of the House's described *2023-onward* sequence. The edited video does not itself enumerate eleven members; the separately attributed 17 April Fox eleven-person list supplies a close chronological and numerical candidate provenance. The narrator's direct sourcing from that article is not independently established.

## Full source-to-claim weld

`AmyEskridgeVideoClaimAttributionLedgerExact`: 86 ordered rows of video statement, speaker, purported carrier, current audit annotation and next receipt.

`AmyEskridgeVideoSourceRegistryExact`: the independently inspected **primary identification or bibliographic/abstract** surfaces (House letter, US patents 1655144, 1655114, 2949550, 3626605, Bem's PubMed abstract); Dan Burisch Project Camelot interview as **testimony**, not physical verification.

`AmyEskridgeVideoClaimProducerWeldExact`: 86 explicit claim joins to actual named *Agda values* in pre-existing source producers where appropriate, otherwise `unpaidCarrier` for the specific claim. Agda `all86RowsAccountedFor = refl` is a finite bookkeeping theorem, **not a source-truth proof**.

`AmyEskridgeVideoTypedObligationWeldExact`: all 86 joins have an explicit typed **remaining** proof-leaf packet; `gateCoverage = refl` ensures none disappears from the research frontier. Unpaid gates are source-identity/recording, roster identity, causal denominator, government programme, experimental data/replication, device/observable, historical full text and energy accounting. New evidence must be admitted by a source-owning module; this video cannot self-certify.

`AmyEskridgeVideoEleventhMediaRosterWeldExact`: reuses the Fox OSINT source atoms and House ten to close the **source-reported** eleven-person member list, with no promotion to primary forensic or targeting evidence.

`AmyEskridgeVideoRosterScopeWeldExact`: imports House, research twenty, original Amy obituary, the roster scope owner, and checked primary House carrier.


## Recovered source: original April 17 Fox eleven-person journalistic list

The original **secondary** source is now located in the existing repo producer `AmyEskridgeOSINTSnowballExact.agda`, not inferred from 10+1 arithmetic:

- **Morgan Phillips**, *11th scientist death emerges in string of missing, dead officials with access to US secrets*, **Fox News Digital**, **2026-04-17 at 11:37 EDT**, https://www.foxnews.com/politics/11th-scientist-death-emerges-string-missing-dead-officials-access-us-secrets.amp.
- **Michael Dorgan**, *White House reviewing cases of missing, dead scientists for possible links as 11th person identified*, **Fox News Digital**, **2026-04-17 at 15:02 EDT**, https://www.foxnews.com/politics/white-house-reviewing-cases-missing-dead-scientists-possible-links-11th-person-identified.amp.

Phillips' named report lists **Eskridge plus Hicks, Reza, McCasland, Maiwald, Grillmair, Loureiro, Chavez, Thomas, Casias and Garcia**. This matches the repo-reconstructed ten-person reporting/House-context set plus Amy. This explicit source closes the **secondary-media attribution and named-list identity** gate that was previously open; `AmyEskridgeVideoEleventhMediaRosterWeldExact.agda` makes the eleven-name typed comparison with the earlier House ten, proves its finite list normalization with `refl`, and retains role distinctions. It **does not** establish the video narrator's actual source, case inclusion endorsed by a primary government agency, all-scientist status, government targeting or common-cause evidence.

Both Fox articles are the **same outlet's reporting**, not two independent forensic witnesses. The April 20 House primary letter (which is later) calls its underlying news reports **unconfirmed** and does not itself add Amy or assert an eleven-person official roster. Fox explicitly reports no publicly available evidence linking Eskridge's death to the others, and no authority-established tie from her research to her death.


## Exact uncut Zoom clip weld (2024 archive; original recording year not independently established)

The existing `AmyEskridgeOSINTSnowballExact.archivedAmyInterviewSource` points to
the [archived Amy Eskridge Zoom transcript](https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom)
by Blocked Epistemology (published **2024-01-27**), identifying original YouTube recording
[video l0O4cEIkUZc](https://www.youtube.com/watch?v=l0O4cEIkUZc), an extended
Zoom conversation among **Amy Eskridge, Jeremy Rys and Mark Sokol**.
The archive explicitly says its automated transcript is not endorsed in entirety.

The new `AmyEskridgeVideoZoomClipSourceWeldExact.agda` binds seven video claim objects
directly to the named **existing** OSINT source owner, including:
| Edited video clip | Original recording time | Source and scope |
|---|---|---|
| 00:00–00:06 | 35:40–35:53 | Amy's reported threat quotation, original speaker testimony, not actor proof |
| 00:05–00:11 | 30:44–31:22 | Amy attributes the purported NSA list of five to a secret-space-program contact, not an NSA document |
| 00:11–00:21 | 34:18–34:38 | Amy quotes the same informant alleging four suppressed discoveries |
| 00:31–01:23 | 2:53:41–2:56:11 | Amy's reported physical surveillance and Lexus licence-plate account |
| 01:41–01:53 | 52:22–52:59 | Amy reports P47/P52 alleged future-human beliefs |

**Exact editing distinction:** the first 21 seconds of the supplied video
are cut as **35:40 → 31:02 → 34:18** from the same original,
instead of the source's chronological **31:02 → 34:18 → 35:40**.
The published uncut recording also provides the alleged informant's attribution
context. The narrated montage therefore rearranges chronology; multiple clips
from the same Amy interview do not represent independent evidence.
This check is a new DASHI editorial-order observation, not a historical claim by Amy.

The Zoom origin is now **source-located** for video rows 001–003, 005–007 and 010.
The respective typed obligation packets no longer charge an unlocated
clip; they retain the independent event, source authenticity,
government-list and physical-proof gates. Source-located dialogue
is NOT proof that the associated physical or intelligence events occurred.

## High-alpha discriminators

1. **Roster source and cardinality.** House ten + Amy = 11 arithmetically; before external sourcing, House ten + Ning Li would also produce 11. **The April 17 Fox report now specifically selects Amy and enumerates ten other names**, closing the bounded secondary media roster membership gate but not the video's provenance or any factual causal connection. The repo's 20 scientific work rows and reconstructed House ten overlap by eight, leaving two House cases outside the retained twenty. The union is 22. Role-inclusive != scientists-only. The two cases outside the 20 are Casias and Garcia.
2. **Patent mismatch.** At video 06:51, US1655144 is attributed to Tesla's space drive; the actual US1655144A patent is Hallgarth/Chandler's *Grain-treating machine*. Tesla US1655114A is a propeller-based aerial-transport patent, **not** an antigravity space drive. Source: respective published USPTO patents, canonical landing copies at https://patents.google.com/patent/US1655144A/en and https://patents.google.com/patent/US1655114A/en.
3. **Podkletnov numerical-source mismatch.** Video 10:43 says approximately 2%. Earlier Podkletnov/Nieminen 1992 paper abstract (DOI **10.1016/0921-4534(92)90055-H**) reports **0.05-0.3%**, **not** 2%. Exact SymPy ratio **2/0.3 = 20/3**. Later claims require their own correctly linked publication; the earlier paper may not be used as a proof of the later 2% figure.
4. **Li NASA work.** NASA NTRS **20000038203**, *Activities of UAH*, cooperative agreement NCC8-124, publicly reports that the planned integrated all-up experiments **could not be completed** during the agreement. https://ntrs.nasa.gov/citations/20000038203. This cannot pay a later AC Gravity/Army success claim.
5. **Project Camelot single-source collapse.** Sixteen video claim rows point to Burisch's **one** interview source family, not sixteen independent witnesses. https://projectcamelot.org/dan_burisch.html. The physics, intelligence and custody claims remain unpaid.
6. **Bem clip mismatch.** NLM PMID **21280961**, DOI **10.1037/a0021524**, establishes an attributed 2011 paper reporting nine psychology experiments, not automatically the video's physiologic anticipatory-arousal clip or a validated forecasting device. https://pubmed.ncbi.nlm.nih.gov/21280961.
7. **Boeing chronology.** The video's claim of an only-2014 GRASP disclosure is contradicted by Nick Cook's report in *Jane's Defence Weekly*, 29 July 2002. The original report needs acquisition/permission-aware inspection; it is not a validated Boeing antigravity apparatus.
8. **Mansfield legislative causal leap.** Do not merge the 1969 historical amendment, later 1973 amendment/versions, alleged public antigravity research suppression and asserted compulsory classification without primary legislation and transaction chains.

## Tested, not tested and acceptance gates

- **Completed now**: source-level linked 86 claims; typed 86 remaining-leaf packets; 10/20 roster source reuse; original House/patent/NLM/NASA metadata and bounded abstract checks; source-count and negative controls.
- **SymPy (run here on manually transcribed source-owner rosters)**: exact set cardinalities 20/10/8/22; alternate eleven-person rosters; Podkletnov 2% versus 0.3% = 20/3; a cited document is logically compatible with absence of causal proof. PASS.
- **GitHub branch static check (run through GitHub source fetch)**: observed all claim001-claim086 and all claimJoin001-claimJoin086, all contiguous; repeated Burisch mapped to 1 source; existing cohort source owners confirm 20, 10, 8, 22. PASS.
- **Full repo SymPy script**: `python scripts/check_amy_eskridge_video_claim_weld_sympy.py`. The code is committed; it has **not** run against a locally checked-out repository in this environment. It should be run before promotion.
- **Agda kernel**: no Agda executable in this environment. Run `DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda`. Do not claim Agda acceptance until an exact-head receipt exists. Separately, existing master imports may refer to files missing from default checkout; investigate those independently rather than adding stubs.

## Next alpha cuts, in order

**G0 — Local gate validation:** run SymPy script and Agda 2.9 target on exact PR head; compare source provenance roles and fix any kernel dependency issues before merge.

**G1 — Original clip acquisition:** original Amy Zoom video, archive and seven clip-time joins are now located and the nonchronological opening splice identified. **Still open:** original edited-video URL/upload/author, complete uncut Burisch/Deutsch/Bem footage locators and independent recordings of claimed events.

**G2 — Eleven-roster attribution:** the April 17 Fox media list now identifies eleven names. Establish whether the narrator actually used that article; continue member-by-member official event, employment and role alignment using existing owners. Assess selection process, population at risk, negative controls and alternative case mechanisms. Never treat House ten plus Amy as an *official* eleven; its membership is attested at Fox newsroom level.

**G3 — Primary full-text source recovery:** HAL5 slide-by-slide source citations; Brown vacuum protocols, Podkletnov later 2% claim, Poher replication, Wallace apparatus, Woodward thrust; full raw data and measurement confounders when available.

**G4 — Government document source exactness:** recover full DIA paper versions and FOIA inventory counts; Boeing 2002 original programme scope, Mansfield legislative versions, Li Army SOW/closeout and NASA Poher test if any.

**G5 — Coupled source-object discriminators:** only after G1–G4, test specific common programme, technical continuity, actual causal event chains and matched-control enrichment. Evidence for a research topic is not an evidence source for suppression.

### Attribution rules (mandatory)
Each joined item must retain **original speaker**, **original source author**, **medium**, **date**, **DOI/patent/canonical link**, **exact bounded result**, **DASHI extension ownership**, **inspection depth**, **negative control** and **unpaid promotion**. A missing DOI is not permission to omit a citation. An original paper's tested regime must not be promoted to a device's observed success. A House request does not certify its referenced journalistic allegations. An unexplained death does not establish targeting. No synthetic witness or derived numerical check may be back-attributed to original authors.


## Source-inspection continuation — original publication and primary documents (2026-11-17)

### Original edited video recovered

- Publisher: **Be Inspired**, YouTube handle `@beinspiredchannel`, video ID `acw16d6CCnY`:
  https://www.youtube.com/watch?v=acw16d6CCnY
- Channel-indexed publication date: **12 May 2026**; full video duration **32:47**. User's timecoded transcript ends at 32:44.
- Independent channel index: https://asknaveen.com/channel/%40beinspiredchannel (12 May 2026, 32:47); a third-party mirror may display 13 May by its timezone. Do not assert an exact timezone of upload without YouTube metadata.
- Original editor/video author **does not become** the author of underlying first-person interview or scientific study. This is a video claim/source aggregator.
- Previous repo notes saying "video URL not supplied" applied **before** this recovery; they are now superseded by the canonical registry and this dated entry.

### Original interview cuts recovered

The new `DASHI/Culture/AmyEskridgeVideoOriginalClipLineageExact.agda` identifies 16 source-clip segments, with exact versus family-only status. These source links remain discoverable:

1. **Amy Eskridge / Jeremy Rys / Mark Sokol, 2020 Zoom**, original https://www.youtube.com/watch?v=l0O4cEIkUZc ; archived full transcript https://blockedepistemology.substack.com/p/archive-amy-eskridge-zoom (archived January 27, 2024). Video 00:00–00:21 combines **out-of-order** quotations from ~30–35 minutes of the Zoom: the source mention of an alleged NSA list is reported hearsay, **not** an inspected NSA document. Video 00:31–01:23 Lexus story draws from ~2:53–2:57 in original. Video 01:41–01:53 P-52 from ~0:52–0:53.
2. **Dan Burisch / Project Camelot 2006**, `Out From Under Majestic`, https://projectcamelot.org/dan_burisch_interview_transcript_2.html ; the video 02:04–02:35 P-45 / 45,000 years exchange matches the section **"2012: Two Timelines"**. This is distinct from:
3. **Dan Burisch / Project Camelot 2007**, `Stargate Secrets`, https://projectcamelot.org/dan_burisch.html ; video 16:02–16:49, 19:15–20:23, 21:22–23:00, 24:00–24:43, 26:39–27:15, 28:41–30:21, 31:26–32:04. Many snippets are now original-interview-family located, but frame-exact source offsets still require original video/audio comparison. Kerry Cassidy and Bill Ryan conducted the interview. Recurrence of one Burisch witness does not create multiple independent sources.
4. **Philip K Dick, 1977 Metz address**, `If You Find This World Bad, You Should See Some of the Others` on video https://www.youtube.com/watch?v=DQbYiXyRZjM ; 16:49–17:13, conceptual/speculative testimony only.
5. **David Deutsch, 17:13–17:40**: voice/theory attributed, **exact original documentary footage not located**. Many-worlds interference is an interpretation of quantum theory; it is not evidence of Looking Glass operations.
6. **18:35–19:10 anticipatory-physiology clip**: original speaker/recording unresolved. Daryl J. Bem, `Feeling the Future` (2011) DOI 10.1037/a0021524 describes nine retroactive psychology tasks; the film's arousal-before-random-images scenario resembles a distinct physiological **presentiment** paradigm associated with Dean Radin and others. Do not attribute this particular clip/experiment to Bem without the source.

### Primary scientific and government source inspections

`DASHI/Culture/AmyEskridgeVideoPrimaryInspectionExact.agda` retains **10 bounded document readings** with documentary locators, exact reported assertions and unpaid stronger claims. It joins the existing 86-row ledger but does not claim physical or forensic validation.

- **NASA cooperative agreement NCC8-124**: Original final report https://ntrs.nasa.gov/api/citations/20000038203/downloads/20000038203.pdf ; Dr Ning Li, dated 4 December 1996–3 December 2000. PDF p.2: two 12-inch YBCO 1-2-3 disks produced; all-up gravitational test apparatus/measurements **not completed** during this agreement. This is direct project documentation, not proof of later Army outcomes. Earlier source owners already cited NTRS 20000038203; this weld adds exact inspected pages.
- **Li, Noever, Robertson, Koczor, Brantley 1997 static YBCO test**: https://ntrs.nasa.gov/citations/19990039542 DOI 10.1016/S0921-4534(97)01462-7, *Physica C* 281, 260–267. Abstract reports detected changes in acceleration **less than 2×10^-8 of g** in its tested static regime. This is a constrained null observation, not a universal disproof of all rotating setups.
- **Noever, Koczor, Roberson rotating-field study (1998)**: NASA NTRS 19990019627 https://ntrs.nasa.gov/citations/19990019627 . The report describes 15 cm YBCO disk, AC rotating field up to 12,000 rpm, and **no noted gravimeter effect** within the tested precision. Exact setup differs from Podkletnov's.
- **Podkletnov & Nieminen (1992)**: DOI 10.1016/0921-4534(92)90055-H, *Physica C* 203, 441–444. Published abstract reports **0.05–0.3% apparent weight** change. Later published accounts (e.g. the Li et al. 1997 introduction) cite reports **0.05–2.1%**. These are *different report lineages*, not a mathematical contradiction or independent replication. Earlier numerical 2% / 0.3% = 20/3 is only a cross-source comparison.
- **DIA FOIA letter** (FOIA-00159-2018): https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf ; issued **25 March 2022**, explicitly enumerates **37 responsive documents / 1,473 pages** and inventory entries #13 (warp), #15 (vacuum metric), #18 (wormholes), #19 (antigravity). A previously circulated **38-title** list is a *different inventory/release stage*, not the number of full 2022 documents. Whether a 38th title was later obtained remains unpaid.
- **Four full DIA Defense Intelligence Reference Documents** are directly inspected in released PDF form, as follows:
  - #13, *Warp Drive, Dark Energy, and the Manipulation of Extra Dimensions* (2 Apr 2010; DIA-08-1004-001), https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_13-DIRD_Warp_Drive_Dark_energy_and_the_Manipulation_of_Extra_Dimensions.pdf . Section 8 (report p.24) discusses a proposed future extra-dimensional propulsion approach. Does not document demonstrated warp control.
  - #15, *Advanced Space Propulsion Based on Vacuum (Spacetime Metric) Engineering* (29 Mar 2010; DIA-08-1003-015), https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_15-DIRD_Advanced_Space_Propulsion_Based_on_Vacuum_Spacetime_Metric_Engineer.pdf . Preface/IV explicit: assumes a hypothetical source capable of modifying metric; required energy densities many orders above engineering feasibility. **A theoretical metric-choice exercise, not a working device**.
  - #18, *Traversable Wormholes, Stargates, and Negative Energy* (6 Apr 2010; DIA-08-1004-004), https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_18-DIRD_Traversible_Wormholes_Stargates_and_Negative_Energy.pdf . Section V (report p.26) outlines steps required for a **future laboratory demonstration**. A diagram or the word 'Stargate' does not establish Burisch's claimed 50 devices.
  - #19, *Antigravity for Aerospace Applications* (30 Mar 2010; DIA-08-1003-018), https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/DIRD_19-DIRD_Antigravity_for_Aerospace_Applications.pdf . Section V (report p.24) explicitly identifies extreme physical scales and **daunting technical challenges**. Does not document a successful antigravity generator.

### Critical open gates after this source welding

- **V1**: Original clip exact-offset receipts for all segments, especially the unidentified Deutsch and physiological-pre-stimulus interview footage.
- **S1**: Primary programme award/statement of work/closeout for Ning Li's post-NASA Army/AC Gravity phase.
- **S2**: Full original experimental datasets/methods for Podkletnov's later 2% tests; independent replications with environmental, electrostatic, temperature, vibration, magnetic and buoyancy controls.
- **S3**: Exact first 38-title DIA inventory vs the 2022 37-document FOIA response; determine missing/unreleased title and custody.
- **S4**: Independent forensic identity/cause evidence for all video roster entries; programme-coincidence and event-time matched controls; no promotion from news selection to harm cause.
- **S5**: Claimed NSA list, Project Camelot device artefacts and EU/UN/NATO custody records: no authenticated primary government/engineering carrier located. Document absence of evidence **is not** proof of concealment.

### Acceptance and epistemic status

The current source checks are **human/automated inspection notes**, **not kernel acceptance**. The SymPy/static checker now additionally asserts: ten explicit inspected-primary records, sixteen original clip records, video publication ID, and the existing 86-claim coverage theorem surface. Run:

```bash
python scripts/check_amy_eskridge_video_claim_weld_sympy.py
DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda
```

Retain **draft** until the checker and full transitive Agda typecheck pass at the exact PR head. No claim about a death, government conspiracy or gravity mechanism is upgraded merely by adding a link.


### Additional exact historical-source controls

- **Podkletnov–Nieminen 1992 original full paper inspected**, publisher *Physica C* 203, 441–444, DOI 10.1016/0921-4534(92)90055-H, document copy: https://robertfrancisjr.com/pdfs/A%20Possibility%20of%20Gravitational%20Force%20Shielding%20by%20Bulk%20Superconductor.pdf . Experimental apparatus: 145 mm by 6 mm YBCO disc, liquid helium, sample 5.47834 g about 15 mm above disc, plastic film and electro-optical balance, rotating field coils. Authors report initial 0.05% apparent weight decrease and 0.3% in stable rotating regime; report fluctuations from -2.5% to +5.4% at other speeds. Their paper states controls for air/static electricity and tests with the disk absent, which should not be silently deleted from an adversarial analysis. Their source still does not supply open raw time-series/covariance, instrument-response or later 2% replication.
- **Mansfield Amendment original government documentation**: U.S. GAO, B-167034, *Implementation of 1970 Defense Procurement Authorization Act Requiring Relationship Of Research To Specific Military Functions*, published **23 June 1970** https://www.gao.gov/products/b-167034 ; Section 203, **Public Law 91-121 (signed November 19, 1969)**, required FY1970 Defense-funded research to relate directly and apparently to military functions. The video asserts "passed in 1973" and jumps to classified black budgets; neither follows from this source. The 1973 version/funding context remains an exact statute-comparison gate.
- **Boeing GRASP contemporary independent reporting**, Nick Cook, *Jane's Defence Weekly*, 29 July 2002, archival original article https://archive.md/lG1GW . Article names Boeing's Phantom Works GRASP effort and a briefing conditional on gravity modification being real. Correct the video's claim of first 2014 acknowledgement, while not promoting the reported *interest* to completed technology.

The new typed module is `DASHI/Culture/AmyEskridgeVideoHistoricalPrimaryControlsExact.agda`. A journal report is attributed to its authors; a government-law summary is attributed to GAO and Congress; the Boeing investigation remains Nick Cook's reporting rather than an authenticated Boeing engineering acceptance document.

### Burisch original transcript passage-level anchors

Project Camelot/Avalon preserve transcripts for separate July 2006 *Out From Under Majestic* and June 2007 *Stargate Secrets*:
- June 2007 *Stargate Secrets* **Part 1**: https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_1_en.html . Direct passage anchors: over 50 devices/ERB (lines 50–76), Stargate/cylinder-seal story (91–109), Yellow Cube (164–186), country elites (284–289), rings/kaleidoscope (537–579), 2017 reassembly prediction (630–663), claimed EU/UN/NATO components (664–671).
- June 2007 **Part 2**: https://projectavalon.net/lang/en/dan_burisch_stargate_secrets_interview_transcript_2_en.html . Frenchman Mountain/portal speculation (431–465).
- July 2006 **Part 2**: https://projectavalon.net/lang/en/dan_burisch_interview_transcript_2_en.html . *2012: Two Timelines* yields P-45 45,000-year original passage.

These locators are now recorded directly in `AmyEskridgeVideoOriginalClipLineageExact.agda`. They pay original oral-source attribution, not any secret agency/machine/custody claim.


## All surrounding primary-source families — original-slide and later-source acquisition (17 November continuation)

This continuation extends the video beyond its 86 explicitly selected claims to all 35 original HAL5 PDF pages and the surrounding source/ref genealogy. It **does not** call a paper or patent a successful experiment merely because it was found. The provenance key for each new file is embedded in the Agda module header, with source-level author/DOI or recoverable URL adjacent to the claim.

### New kernel-facing source owners (this PR)

| Module | New typed scope and strongest exact proof | Status |
|---|---|---|
| `AmyEskridgeVideoHAL5AllSlidesExact` | All **35 one-based original PDF pages**, with source-author identity, video-claim referents, and `entireOriginalDeckCovered = refl` | Metadata/deck coverage, not real device test |
| `AmyEskridgeVideoDIAFullInventoryExact` | All **37 DIA FOIA report titles** with individual printed page counts; `exactInventoryCount = refl`, `exactInventoryListedPageTotal = refl` for **1,473** pages | Four original bodies read; 33 inventory titles only |
| `AmyEskridgeVideoSurroundingSourceAtlasExact` | **42 DOI/canonical-URL source-family entries** from patent, original article, government, documentary, and institutional sources; `sourceFamilyCount = refl` | Inspection depth varies per original |
| `AmyEskridgeVideoSurroundingProducerWeldExact` | **39 high-alpha video claim routes** to exact existing Agda original-paper, lab-constraint, Army administrative, Texas audit, HAL5 slide and DIA inventory objects; `exactSourceScopedWeldCount = refl` | Additional typed provenance, not replacement for all 86 joins |
| `AmyEskridgeVideoOmittedOriginalResearchWeldExact` | **Eight additional original paper/report/abstract atoms** overlooked in edited video; `allAdditionalSourcesIndexed = refl` | Participant claims, conference abstracts or source locators, independent scientific proof open |
| `AmyEskridgeVideoEvidenceEverything` | Imports all new modules into the existing video → Eskridge → missing/deceased investigation, without forking a separate scientific lane | Structural aggregator |

Previous explicit 86 claim-to-source joins and 86 independent typed open-obligation packets remain in force. The new surrounding *source* atlas does not imply that 42 independent empirical studies reported positive results; it is a heterogeneous bibliography with multiple source classes and inspection depths.

### Sources omitted in the edited video, with direct original document owners

1. **John Searl / Sandberg:** S. Gunnar Sandberg, *The Searl Effect & The Searl-Effect Generator*, 17 June **1987**, original archived report https://toba60.com/wp-content/uploads/2020/07/John-Searl-The-Searl-Effect-The-Searl-Effect-Generator.pdf ; author states reconstruction comes from Searl interviews beginning in 1982 and says the original 1946–52 experimental documents were reportedly destroyed in a 1983 fire. This is reported source-history, not independent confirmation of a levitating generator. `Slides.deck16`.
2. **Hutchison primary participant:** G. Hathaway, *Hutchison Effect Metal Samples: Description and Analysis*, *Materials Science & Technology 2009* pp.667–678, author full paper http-independent archive copy https://ia902306.us.archive.org/1/items/g-hathaway-hutchison-metal-analysis/G.%20Hathaway%20Hutchison%20Metal%20Analysis%20-%20cp2009mst0667%20ASM%20int.%20-%20Enrico.pdf . Hathaway describes the apparatus, first-person witnesses and inability to make effects repeatable/controllable, despite sample analyses and photographs. Source archive https://hutchisonfiles.com/sources/ distinguishes involved witness from outside-lab replication. Also earlier involved Hathaway, *The Hutchison Effect — A Lift and Disruption System* (1990) at https://gbppr.net/hutchinson/The-Hutchison-File.pdf . `Slides.deck22`.
3. **Torr, Vargas and Datta:** Timir Datta, Ming Yin and José Vargas, *A Gravitational Experiment Involving Inhomogeneous Electric Fields*, **STAIF-2004 abstract p.240** inside a publicly accessible NASA-GSFC-hosted proceedings volume, https://science.gsfc.nasa.gov/attic/ants/documents/staif2004spacepower.pdf ; discusses authors' **preliminary correlation** between applied inhomogeneous E field and measured force, claimed mass scaling. This is NOT an inspected complete experimental paper nor an endorsed NASA test. Direct prior art US6891712B2 and US7327548B2 belongs to **Douglas Torr and José Vargas**, not Timir Datta (who is a different coauthor on the abstract). `Slides.deck27`.
4. **Morningstar:** P. A. Murad and J. E. Brandenburg, *A Nonlinear Electromagnetic Device and Potential Explanations*, *Journal of Multidisciplinary Engineering Science Studies* **6(12), December 2020**, original article https://www.jmess.org/wp-content/uploads/2020/12/JMESSP13420694.pdf . Authors report an approximately **190-pound Energy Box**, **7%** apparent steady-state weight loss and **20%** transients, and expressly admit **self-acceleration was NOT achieved**. The percentages are **authors' observations**, not independently calibrated gravity effects. Prior AIAA-2012-0998, *The Morningstar Energy Box*, 2012, identified by Murad's later proposal bibliography https://kepleraerospace.com/wp-content/uploads/2023/03/NASA-NSPIRES-DraftProposal.pdf ; original full AIAA paper remains acquisition. The earlier paper's author list must not be falsely substituted for the 2020 Murad/Brandenburg article. `Slides.deck30`.
5. **Giovanni Modanese independent research identity:** Giovanni Modanese and Giorgio Fontana, *Effect of the Vacuum Energy Density on Gravitation Propagation*, **STAIF-2004 abstract p.239** in the same NASA-GSFC hosted volume. The original abstract is an explicitly conditional theoretical discussion and cannot be used as proof that the video narrator's Wikipedia-page deletion claim is accurate. `Slides.deck28`.
6. **Woodward independent presentation:** Paul March, *Woodward Effect Experimental Verifications*, **STAIF-2004 abstract p.241**, same NASA-GSFC hosted volume. It announces initial tests and future presentation of results, but the abstract is **not** a complete independently verified propulsion measurement; this distinct author/source object must not be back-attributed to Woodward's original 1992 theoretical paper. `Slides.deck23`.

### Full DIA inventory and specific source limitation

The March 25, 2022 DIA response https://documents2.theblackvault.com/documents/dia/AAWSAP-DIRDs/FOIA%2000159-2018.pdf supplies 37 numbered DIRDs totalling 1473 pages. We transcribed **all 37 titles** and *all* listed page counts. Reports **#13, #15, #18, #19** are marked full-body inspected in the existing primary-inspection module. The other **33 remain inventory metadata**. Additional scientific-seeming titles in the inventory — **#14 Role of Superconductors in Gravity Research; #24 Concepts for Extracting Energy from the Quantum Vacuum; #29 Negative Mass Propulsion; #36 Quantum Tomography of Negative Energy States in the Vacuum** — are explicitly indexed but not upgraded to inspected full-text reports. Exact 38-title variant provenance remains open.

### Current exact proof / experimental boundary

- The original Podkletnov/Nieminen **1992** 0.05–0.3% observation and the later Podkletnov **1997** 1.9–2.1% report are two different original-source claims. The **2003 Hathaway/Cleveland/Bao null to 0.001%** tested a different rpm regime; it is relevant evidence but not a universal same-apparatus falsification.
- NASA's Ning Li 1997 static null, NASA 1998 rotating-field null, 2000 NCC8-124 report of incomplete all-up test, and 2001 uninspected FY01RPT archive are separate empirical/administrative objects. The exact **DAAH01-01-9-R001** identifier also appears in Texas 2005/2006 Lockheed pass-through accounts, but the repository's source owner explicitly marks its **same-object identification false/unpaid**. Do not infer Lockheed/AC Gravity collaboration from the matching digits.
- Deleted Wikipedia entries, P-45/P-52, TR-3B craft, Morningstar physics, YouTube narrative, and 2015 NASA testing of Poher apparatus all retain distinct unverified proof leaves. The 2004 conference proceedings as **NASA-hosted** does **not** mean **NASA-sponsored, tested or approved** its published claims.

### SymPy and structural acceptance

Executed exact SymPy arithmetic in the current work environment (SymPy 1.14): **37 DIA items, exactly 1,473 pages, four original report bodies, 33 titles only**; verified the original/later Podkletnov result intervals and independent Hathaway 0.001% sensitivity distinction (without asserting equal experimental geometries). Additional branch-source static checks in the GitHub-accessible source confirmed **86 claims, 86 original joins, 35 slides, 37 DIRDs, 42 source entries, 39 additional claim-producer welds and eight omitted-source report entries**; all symbol references to the existing source and experiment owner modules were verified. These are source-structure checks, **not Agda 2.9 kernel acceptance**. Running committed Python against an actual repository checkout remains pending because the model runtime has no GitHub network checkout and no Agda compiler.

The extended `scripts/check_amy_eskridge_video_claim_weld_sympy.py` now incorporates these exact expected counts, original producer presence, no-unjustified-promotion controls and source-reference regression. Validate on exact PR head locally:

```bash
python scripts/check_amy_eskridge_video_claim_weld_sympy.py
DASHI_NO_TMUX=1 scripts/run_agda29_parallel_check.sh DASHI/Culture/AmyEskridgeVideoEvidenceEverything.agda
```

**High-alpha remaining:** original full FY01RPT.doc row and Army closeout, Morningstar 2012 AIAA complete experiment/logs, Datta/Yin/Vargas full results and independent controls, Searl surviving contemporaneous production documents, Hutchison independently blinded apparatus tests, original Deutsch/presentiment *frame-exact* audio comparison, original B-167034/1973 variant precise statute coverage, and the video eleven-person same-cause discriminator. No promotion from citations to confirmed gravity engineering, classified programmes or event causation.
