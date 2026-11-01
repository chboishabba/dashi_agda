module DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact where

open import DASHI.Core.Prelude

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- QUANTITATIVE EFFECT-SIZE PILOT
--
-- Same-object MDPI source: DOI 10.3390/su16041674.
-- This fixture tests the positive path where a source reports a group/time
-- contrast and explicit effect-size statistics while still leaving the exact
-- inferential analysis denominator unresolved in the visible primary text.
------------------------------------------------------------------------

brasslerPilotProfile : Ceiling.StudyClaimProfile
brasslerPilotProfile = Ceiling.study-claim-profile
  "brassler-2024-oer-digital-competence"
  Correction.brasslerOERESDPublisherSpellingSource
  "candidate quantitative quasi-experimental / bounded-contrast evidence"
  "10.3390/su16041674; Sample and Design 5.1; Instruments 5.2; Results 6; Limitations 7.2"
  "two-group pretest-posttest comparison of OER-production students and same-cohort students enrolled in discipline seminars unrelated to OER content development"
  (Ceiling.sourceReportedDesignUnmapped
    "quasi-experimental two-group pretest-posttest design"
    "the source itself calls the design quasi-experimental in its limitations and explicitly notes group-equivalence and self-selection threats; no randomized allocation is inferred")
  "409 University of Hamburg students across Psychology, Economics, Educational Sciences and Geosciences: 83 OER-production-course students and 326 same-cohort controls"
  (Ceiling.explicitlyReportedNat 409 "study sample: 83 OER-production students + 326 control-group students")
  (Ceiling.natNotReported "article reports N=409 but repeated-measures ANOVA F(1,191); visible primary text does not explain the inferential analysis denominator, so analysis n is not reconstructed from degrees of freedom")
  "course participation was not reported as randomized; self-selection/group-equivalence threats are explicitly acknowledged"
  "OER-production course versus same-cohort discipline seminars unrelated to OER content development"
  "five-item Creative Internet Skills Scale; German translation/back-translation reported above 90% literal/contextual equivalence; internal consistency alpha=.84 at baseline and .88 post-course"
  "the visible primary text does not report the missing-data mechanism that reconciles N=409 with F(1,191); this discrepancy remains acquisition debt"
  "source explicitly notes quasi-experimental group-equivalence and self-selection threats; control group is substantially larger than the OER group"
  "semester course follows constructive-alignment design with OER production, interdisciplinary peer learning, technical expertise on demand, feedback loops and product-based grading; no independent fidelity estimate is reported"
  "one principal repeated-measures model is reported for digital competence; this pilot does not invent a multiplicity correction beyond the source's analysis"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "Time main effect F(1,191)=59.7, p<0.001, partial eta-squared=.238; Time×Group interaction F(1,191)=22.4, p<0.001, partial eta-squared=.105; group means OER 2.49→3.42, control 2.22→2.54"
    "Results 6 / Table 1"
    "partial eta-squared values are source-reported effect sizes for the fitted repeated-measures model; they are not converted into causal population effects")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "p<0.001 is reported for both the Time main effect and Time×Group interaction; no confidence interval for the educational effect is reported in the visible primary article text"
    "Results 6"
    "significance plus partial eta-squared pays bounded model contrast/effect magnitude, not a confidence interval, causal identification, population transport or system transformation")
  "beginning to end of one semester; no longitudinal follow-up beyond the course"
  "one University of Hamburg setting and four disciplines; source explicitly identifies quasi-experimental/self-selection limits, so external transport remains unpaid"
  (Ceiling.reportedEpistemicRole Design.informant
    "students provide self-reported digital-competence questionnaire data and produce OERs; this does not create participant governance authority")
  (Ceiling.implicationConeClaim Cone.derivesBoundedContrast)
  "supports a bounded within-study claim that digital competence increased more over the semester in the OER-production group than in the same-cohort comparison group, with reported medium Time×Group effect size; the design does not independently identify a population causal effect"
  "quasi-experimental/self-selected groups; unexplained N=409 versus F(1,191) analysis-denominator discrepancy; self-report measure rather than objective performance; no effect CI; one-semester horizon; no universal transport"

quantitativePilotStatus : String
quantitativePilotStatus =
  "pre-screen method-validation profile only; exact source identity, sample statement, reported model/effect sizes and explicit limitations are retained, but final manuscript inclusion and unresolved analysis-n acquisition remain separate obligations"
