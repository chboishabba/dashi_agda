module DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- QUANTITATIVE UNCERTAINTY ACQUISITION
--
-- Primary source:
--   Wen-Jing Deng; Jiayue Sun; Wingkei Ho; John Chi-Kin Lee
--   "Short-Term Knowledge Gains and Regional Heterogeneity in a STEM-Based
--    Indoor Air Quality Education Intervention for Sustainability Across Asian
--    Regions"
--   Sustainability 18(14), 7165 (2026)
--   DOI 10.3390/su18147165
--
-- This source is acquired specifically to exercise the positive statistical
-- path: reported sample size + pre/post contrast + effect size + 95% CI.
-- The absence of a comparison group is retained as a hard causal ceiling.
------------------------------------------------------------------------

iaqSustainabilityEducationSource : Attr.AttributedSource
iaqSustainabilityEducationSource =
  Attr.mkDOISource
    "Wen-Jing Deng; Jiayue Sun; Wingkei Ho; John Chi-Kin Lee"
    "Short-Term Knowledge Gains and Regional Heterogeneity in a STEM-Based Indoor Air Quality Education Intervention for Sustainability Across Asian Regions"
    "Sustainability 18(14), 7165"
    "2026"
    "10.3390/su18147165"
    "https://doi.org/10.3390/su18147165"
    Attr.academicArticleSource
    "Primary short-term pre/post sustainability-education program evaluation across five Asian regions. Supports source-bounded knowledge-gain, regional-heterogeneity, effect-size and interval claims only; no comparison group means the source does not independently identify a causal intervention effect or long-term behavioural change."
    Attr.publicAttribution

iaqPilotProfile : Ceiling.StudyClaimProfile
iaqPilotProfile = Ceiling.study-claim-profile
  "deng-sun-ho-lee-2026-iaq-sustainability-education"
  iaqSustainabilityEducationSource
  "candidate quantitative short-term program-evaluation evidence with explicit effect size and confidence interval"
  "10.3390/su18147165; Abstract; Methods; Results"
  "pre-test/post-test program evaluation of immediate indoor-air-quality knowledge change across five regional student cohorts; no untreated or alternative-intervention comparison group"
  (Ceiling.sourceReportedDesignUnmapped
    "multi-region one-group pretest-posttest program evaluation"
    "the source reports paired pre/post change, regional heterogeneity, regression and sensitivity analyses but no comparison group; do not promote the design to a controlled causal experiment")
  "1408 Grades 5-10 students: Sri Lanka n=395, Nepal n=300, Malaysia n=314, Indonesia n=200, and Guangxi China n=199"
  (Ceiling.explicitlyReportedNat 1408 "Grades 5-10 students across five Asian regions")
  (Ceiling.explicitlyReportedNat 1408 "primary overall pre/post program-evaluation sample reported in the source abstract")
  "no treatment/control allocation; all analysed cohorts received the STEM-based IAQ education program"
  "within-student pre/post comparison plus between-region heterogeneity analyses; no non-intervention control group"
  "primary outcome is IAQ knowledge score gain on a 0-100 scale; paired t-tests, regional ANOVA/Kruskal-Wallis, BH-adjusted Welch pairwise tests, OLS gain models and sensitivity analyses are reported"
  "the source reports sensitivity analysis excluding post-test zero records with nonzero pre-test values; this is retained as a data-quality sensitivity rather than silently deleting the issue"
  "no untreated comparison means secular/testing/history effects remain live causal alternatives; baseline score and region are modelled as predictors rather than eliminating all confounding"
  "short standardized education program evaluated immediately; the source itself calls for stronger future implementation-fidelity measures"
  "regional pairwise comparisons use BH adjustment; multiple regional/outcome analyses remain part of the declared statistical surface"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "overall mean knowledge gain +9.25 points with Cohen's dz=0.289; regional gains: Nepal +22.25, Indonesia +15.93, Sri Lanka +5.39, Malaysia +5.36, Guangxi -3.27; regional heterogeneity ANOVA eta-squared=0.070"
    "Abstract / Results"
    "effect sizes quantify observed short-term change and regional heterogeneity under the study design; they do not identify a counterfactual causal effect without a comparison group")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "overall mean gain +9.25, 95% CI [7.58,10.92], p=2.30e-26, dz=0.289; regional heterogeneity ANOVA F=26.55, p=2.98e-21 and Kruskal-Wallis H=84.95, p=1.56e-17"
    "Abstract / Results"
    "the 95% CI is an interval for the observed paired mean gain under the reported analysis; it does not manufacture a causal treatment-effect interval, long-term persistence, behavioural change or population transport")
  "immediate short-term pre/post assessment only; no delayed follow-up"
  "five Asian regional cohorts with substantial contextual heterogeneity; no general transport beyond the sampled grades/regions without separate evidence"
  (Ceiling.reportedEpistemicRole Design.informant
    "students provide the assessed knowledge responses; this participant role does not create intervention-governance authority")
  (Ceiling.implicationConeClaim Cone.derivesBoundedContrast)
  "supports a bounded paired pre/post knowledge-gain estimate with explicit effect size and 95% interval plus evidence of substantial regional heterogeneity; does not independently support a causal intervention-effect claim because no comparison group is present"
  "one-group pre/post design; immediate knowledge outcome only; no behavioural outcome or delayed post-test; no comparison group; regional heterogeneity is large; sensitivity to post-test zero records is material; stronger fidelity and causal designs are explicitly left for future work"

iaqAcquisitionReading : String
iaqAcquisitionReading =
  "This source pays the review's previously unexercised positive statistical path: exact source attribution, n=1408, an observed pre/post effect magnitude, Cohen's dz and a 95% confidence interval. The interval belongs to the paired knowledge-gain estimand under a one-group pre/post program evaluation. It does not become a causal treatment-effect interval merely because it is precise or statistically significant."
