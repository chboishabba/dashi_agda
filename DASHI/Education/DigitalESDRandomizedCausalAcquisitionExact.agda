module DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Reasoning.EvidenceDesignAdmissibilityExact as Design
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- RANDOMIZED ESD ACQUISITION WITH CAUSAL-PROMOTION AUDIT
--
-- Primary source:
--   Caroline Green; Owen Molloy; Jim Duggan
--   "An Empirical Study of the Impact of Systems Thinking and Simulation on
--    Sustainability Education"
--   Sustainability 14(1), 394 (2022)
--   DOI 10.3390/su14010394
--
-- The design randomizes participants to four factorial groups. However, the
-- reported inferential contrasts exclude outliers / non-engaged records after
-- randomization. This profile therefore retains randomization as a strong design
-- receipt while leaving the full causal promotion unpaid at this extraction
-- stage. Randomized design != automatic causal authority for every analyzed
-- contrast.
------------------------------------------------------------------------

greenMolloyDugganSource : Attr.AttributedSource
greenMolloyDugganSource =
  Attr.mkDOISource
    "Caroline Green; Owen Molloy; Jim Duggan"
    "An Empirical Study of the Impact of Systems Thinking and Simulation on Sustainability Education"
    "Sustainability 14(1), 394"
    "2022"
    "10.3390/su14010394"
    "https://doi.org/10.3390/su14010394"
    Attr.academicArticleSource
    "Primary randomized 2x2 factorial online ESD trial. Supports source-bounded randomized-design, quiz-score contrast, effect-size and analysis-procedure claims. Post-randomization exclusions/outlier handling and construct/transport limits remain explicit; the source does not automatically pay population transport or system transformation."
    Attr.publicAttribution

greenMolloyDugganPilotProfile : Ceiling.StudyClaimProfile
greenMolloyDugganPilotProfile = Ceiling.study-claim-profile
  "green-molloy-duggan-2022-systems-simulation-rct"
  greenMolloyDugganSource
  "candidate randomized-factorial ESD learning evidence with conservative causal-promotion audit"
  "10.3390/su14010394; Methods 4.2/4.6; Results 5.1-5.2; Table 6"
  "randomized two-by-two factorial online sustainability-learning trial testing systems-thinking and system-dynamics-simulation factors"
  (Ceiling.sourceReportedDesignUnmapped
    "randomized controlled 2x2 factorial trial"
    "random assignment is explicit, but the reported outcome contrasts include post-randomization outlier/non-engagement exclusions; retain source-reported design while the profile separately records the analyzed sets")
  "227 signed up; 80 did not follow up, 8 started then withdrew, 33 datasets were incomplete/invalid; after validation 106 complete participant datasets remained and were randomly assigned to four groups"
  (Ceiling.explicitlyReportedNat 106 "randomised controlled factorial trial total n")
  (Ceiling.natNotReported "106 complete randomized datasets exist, but reported inferential contrasts use analysis-local exclusions (e.g. simulation 24 vs control 27 after control outlier removal); no single analysis n represents all reported tests")
  "participants were randomly assigned to control, systems-thinking, simulation, or systems-thinking-plus-simulation groups; full validated groups were 28/26/24/28"
  "factorial control and treatment groups saw different combinations of systems-thinking and simulation content; all groups completed the same quizzes"
  "two sustainability quiz outcomes; quizzes/surveys were refined by pilot testing and source data are reported as openly available; the profile limits interpretation to the measured quiz-score construct rather than treating it as exhaustive sustainability competence"
  "pre-randomization recruitment loss is substantial; after validation 106 complete datasets remained. For inferential testing a Quiz-1 control outlier was removed, the extreme Quiz-2 control outlier was removed, and two Quiz-2 datasets were removed after analytics showed non-engagement with the fisheries section"
  "random assignment supports treatment-balance intent, but analysis-local post-randomization exclusions remain a causal-promotion residual in this review profile"
  "single online learning session with controlled factor exposure; page analytics were used to identify non-engagement for part of the transfer analysis"
  "one-tailed Wilcoxon tests use Bonferroni correction for relevant pairwise comparisons; factorial ANOVA assumptions were checked with Levene and Shapiro-Wilk tests and non-parametric alternatives used when required"
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "Quiz-1 simulation group n=24, M=78.4, SD=14.1 versus analyzed control n=27, M=71.9, SD=9.3; p=0.018 after Bonferroni-adjusted one-tailed Wilcoxon comparison; Cohen's d=0.6. Systems-thinking-only d=0.4 with p=0.247; combined-factor d=0.1 and negative interaction p=0.045"
    "Results / Table 6"
    "reported effect sizes are bounded to immediate measured quiz performance under the analyzed contrast; no universal ESD-effect magnitude is inferred")
  (Ceiling.reported-surface Ceiling.explicitlyReported
    "source reports p=0.018 at alpha=0.05 for the immediate simulation contrast; it does not report a numerical confidence-interval endpoint for Cohen's d or the group mean difference. Transfer Quiz-2 simulation contrast reports p=0.0787 at the 95% level and d=0.4"
    "Results / Table 6"
    "a statement that a test is judged at the 95% confidence level is not represented as a 95% confidence interval when interval endpoints are absent")
  "single-session immediate Quiz-1 effect; Quiz-2 tests near-term knowledge transfer within the same study, not delayed longitudinal persistence"
  "mostly Ireland/UK, highly educated adult volunteer sample with average age around 50; no population transport to school-age or general university ESD populations is created"
  (Ceiling.reportedEpistemicRole Design.informant
    "participants provide quiz/survey responses; random assignment does not create governance or interpretive authority")
  (Ceiling.implicationConeClaim Cone.associatesTreatmentAndOutcome)
  "supports a strong randomized-design association between simulation exposure and higher immediate measured sustainability-quiz scores in the reported analyzed contrast, with d=0.6 and p=0.018; this profile conservatively leaves full causal promotion unpaid because the inferential contrast is post-randomization-exclusion-sensitive and the measured quiz is narrower than sustainability competence"
  "volunteer/recruitment funnel 227→106 complete datasets; analysis-local outlier/non-engagement exclusions; no numerical effect CI; single-session horizon; predominantly Ireland/UK highly educated adult sample; quiz construct is not exhaustive sustainability competence; transfer outcome is weaker at p=0.0787"

randomizedCausalResidual : String
randomizedCausalResidual =
  "Randomization is retained as a strong design receipt, but the review does not promote the source to attributesCausalEffect merely from the RCT label. The analyzed RQ2 contrast excludes a randomized control outlier and later transfer analysis removes further records. A future causal promotion would require an explicit consumer decision about the estimand/analysis set and the admissibility of those post-randomization exclusions; it would still remain bounded to the measured quiz outcome and sampled population."
