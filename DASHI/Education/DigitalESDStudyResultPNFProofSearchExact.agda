module DASHI.Education.DigitalESDStudyResultPNFProofSearchExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Education.DigitalESDStudyClaimCeilingExact as Ceiling
import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact as IAQ
import DASHI.Education.DigitalESDStudyClaimQuantitativePilotExact as Brassler
import DASHI.Education.DigitalESDStudyClaimPilotExact as Pilot
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as Green
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- STUDY RESULT -> PNF -> IMPLICATION / PROOF-SEARCH FRONTIER
--
-- This owner does not infer a paper's meaning from its title or discussion.
-- Each fixture starts from a source-local result already extracted into the
-- study-claim profile, normalises that result into explicit population,
-- context, intervention, comparator, outcome, time and inferential-force
-- coordinates, then states the strongest implication paid by those receipts.
-- The first stronger unpaid implication is retained as proof-search debt.
------------------------------------------------------------------------

record StudyResultAudit : Set where
  constructor study-result-audit
  field
    studyKey : String
    profile : Ceiling.StudyClaimProfile
    assertion : PNF.PredicateNormalAssertion
    statisticalReceipt : String
    uncertaintyReceipt : String
    strongestPaidImplication : Cone.ImplicationKind
    strongestPaidReason : String
    firstUnpaidImplication : Cone.ImplicationKind
    firstUnpaidReason : String
    promotionResidual : String

open StudyResultAudit public

------------------------------------------------------------------------
-- Deng, Sun, Ho & Lee 2026: observed paired knowledge gain.
------------------------------------------------------------------------

iaqScope : PNF.AssertionScope
iaqScope = PNF.assertionScope
  "1408 Grades 5-10 students across five sampled Asian regions"
  "Sri Lanka, Nepal, Malaysia, Indonesia and Guangxi (China)"
  "STEM-based indoor-air-quality sustainability education programme"
  "same students before the programme; no non-intervention comparison group"
  "immediate IAQ knowledge score on a 0-100 scale"
  "immediate pre-test to post-test"

iaqPredicates : List PNF.PredicateAtom
iaqPredicates =
  PNF.predicateAtom "sampled-student" PNF.populationPredicate "student × sampled-region"
    "student belongs to the reported analysed Grades 5-10 regional sample"
  ∷ PNF.predicateAtom "received-programme" PNF.interventionPredicate "student × programme"
    "the analysed student received the STEM-based IAQ education programme"
  ∷ PNF.predicateAtom "paired-pre-post" PNF.comparatorPredicate "student × pre-score × post-score"
    "the comparison is within-student pre-test versus post-test, not treatment versus untreated control"
  ∷ PNF.predicateAtom "knowledge-gain" PNF.outcomePredicate "student × IAQ-knowledge-score"
    "the reported outcome is change in immediate IAQ knowledge score"
  ∷ PNF.predicateAtom "short-term" PNF.temporalPredicate "programme × assessment-time"
    "the outcome is measured immediately after the programme without delayed follow-up"
  ∷ PNF.predicateAtom "bounded-estimate" PNF.significancePredicate "paired-mean-gain × uncertainty"
    "overall reported mean gain is +9.25 points with 95% CI [7.58,10.92], p=2.30e-26 and Cohen's dz=.289"
  ∷ []

iaqObservedGainAssertion : PNF.PredicateNormalAssertion
iaqObservedGainAssertion = PNF.predicateNormalAssertion
  "deng-2026-iaq-observed-paired-gain"
  "In the analysed five-region student sample, immediate post-programme IAQ knowledge scores were higher than pre-programme scores by a reported mean 9.25 points."
  PNF.studyPopulationQ
  PNF.comparativeF
  iaqScope
  iaqPredicates
  "same-object DOI 10.3390/su18147165; profile retains n=1408, paired gain, CI, effect size and no-control limitation"

iaqResultAudit : StudyResultAudit
iaqResultAudit = study-result-audit
  "deng-sun-ho-lee-2026-iaq"
  IAQ.iaqPilotProfile
  iaqObservedGainAssertion
  "n=1408; mean paired gain +9.25 points; Cohen's dz=.289; regional heterogeneity eta-squared=.070"
  "95% CI [7.58,10.92] for the observed paired mean gain; interval is not a counterfactual treatment-effect interval"
  Cone.derivesBoundedContrast
  "same-student pre/post data plus explicit effect/interval receipts pay a bounded observed contrast"
  Cone.attributesCausalEffect
  "no untreated or alternative-intervention comparator; testing/history/secular explanations remain live"
  "next causal probe would require a design that identifies the counterfactual programme effect; more precision on the paired gain cannot substitute for that comparator"

------------------------------------------------------------------------
-- Braßler 2024: Time x Group interaction in a quasi-experiment.
------------------------------------------------------------------------

brasslerScope : PNF.AssertionScope
brasslerScope = PNF.assertionScope
  "University of Hamburg students in the reported OER-production and same-cohort comparison groups"
  "one university, four disciplines"
  "semester OER-production course"
  "same-cohort discipline seminars unrelated to OER content development"
  "self-reported Creative Internet Skills Scale digital competence"
  "beginning to end of one semester"

brasslerPredicates : List PNF.PredicateAtom
brasslerPredicates =
  PNF.predicateAtom "course-group" PNF.populationPredicate "student × course-group"
    "student is in the reported OER-production or comparison group"
  ∷ PNF.predicateAtom "oer-production" PNF.interventionPredicate "student × semester-course"
    "OER-group students participate in the OER-production course"
  ∷ PNF.predicateAtom "same-cohort-comparator" PNF.comparatorPredicate "student × group"
    "comparison group comprises same-cohort discipline-seminar students rather than randomized controls"
  ∷ PNF.predicateAtom "digital-competence-score" PNF.outcomePredicate "student × Creative-Internet-Skills-Scale"
    "outcome is the source-reported five-item self-report digital-competence score"
  ∷ PNF.predicateAtom "time-by-group-interaction" PNF.significancePredicate "time × group × fitted-model"
    "source reports F(1,191)=22.4, p<.001 and partial eta-squared=.105 for Time x Group"
  ∷ PNF.predicateAtom "quasi-experimental-selection" PNF.contextPredicate "allocation × group-equivalence"
    "course participation was not randomized and source explicitly retains self-selection/group-equivalence threats"
  ∷ []

brasslerInteractionAssertion : PNF.PredicateNormalAssertion
brasslerInteractionAssertion = PNF.predicateNormalAssertion
  "brassler-2024-time-group-digital-competence"
  "Within the reported quasi-experimental model, digital-competence scores increased more over the semester in the OER-production group than in the same-cohort comparison group."
  PNF.studyPopulationQ
  PNF.comparativeF
  brasslerScope
  brasslerPredicates
  "same-object DOI 10.3390/su16041674; study N=409 retained while inferential analysis N remains unresolved"

brasslerResultAudit : StudyResultAudit
brasslerResultAudit = study-result-audit
  "brassler-2024-oer-digital-competence"
  Brassler.brasslerPilotProfile
  brasslerInteractionAssertion
  "study N=409; Time F(1,191)=59.7, p<.001, partial eta-squared=.238; Time x Group F(1,191)=22.4, p<.001, partial eta-squared=.105"
  "no numerical educational-effect confidence interval reported in the visible primary text; analysis denominator behind F(1,191) remains acquisition debt"
  Cone.derivesBoundedContrast
  "reported group/time model and effect magnitude pay a within-study comparative interaction claim"
  Cone.attributesCausalEffect
  "self-selection and unresolved group equivalence prevent the observed interaction from independently identifying a population causal effect"
  "next useful acquisition is the same-object missing-data/analysis-set account behind the N=409 versus F(1,191) discrepancy; even paying that would not itself remove non-random allocation"

------------------------------------------------------------------------
-- Descamps et al. 2025: two active digital-sobriety scenarios.
------------------------------------------------------------------------

descampsScope : PNF.AssertionScope
descampsScope = PNF.assertionScope
  "107 complete pre/post first-year university student cases"
  "University of Mons, Belgium"
  "digital-sobriety learning intervention with individual-action or collective-action scenario"
  "individual-action scenario versus collective-action scenario; both are active intervention conditions"
  "digital-sobriety maturity, motivation and collective-efficacy questionnaire outcomes"
  "single learning session with immediate pre/post assessment"

descampsPredicates : List PNF.PredicateAtom
descampsPredicates =
  PNF.predicateAtom "complete-pre-post-case" PNF.populationPredicate "student × measurement-pair"
    "student has both pre-test and post-test data in the analysed n=107 complete-case set"
  ∷ PNF.predicateAtom "scenario-assignment" PNF.interventionPredicate "student × scenario"
    "analysed students were reported as randomly divided between two active scenario conditions"
  ∷ PNF.predicateAtom "active-scenario-comparison" PNF.comparatorPredicate "individual-action × collective-action"
    "comparison is between two active pedagogical scenarios, not intervention versus no intervention"
  ∷ PNF.predicateAtom "maturity-gain" PNF.outcomePredicate "student × digital-sobriety-maturity"
    "source reports relative maturity gains of 27.63% and 25.85% across the two scenario groups"
  ∷ PNF.predicateAtom "group-contrast" PNF.significancePredicate "scenario × reported-test"
    "maturity comparison W=1531, p=.051; other reported contrasts include p=.038, p=.015 and p<.001"
  ∷ PNF.predicateAtom "complete-case-loss" PNF.contextPredicate "session-participants × analysed-cases"
    "164 students participated but only 107 complete pre/post cases entered analysis"
  ∷ []

descampsScenarioAssertion : PNF.PredicateNormalAssertion
descampsScenarioAssertion = PNF.predicateNormalAssertion
  "descamps-2025-active-scenario-contrast"
  "Among complete pre/post cases, the two active digital-sobriety scenarios showed similar maturity gains, while some motivation and collective-efficacy contrasts differed between scenario groups."
  PNF.studyPopulationQ
  PNF.comparativeF
  descampsScope
  descampsPredicates
  "same-object DOI 10.1186/s41239-025-00569-3; n=164 session participants, n=107 complete pre/post cases, active-scenario groups 57 and 50"

descampsResultAudit : StudyResultAudit
descampsResultAudit = study-result-audit
  "descamps-2025-digital-sobriety"
  Pilot.descampsPilotProfile
  descampsScenarioAssertion
  "164 session participants; 107 complete pre/post cases; active groups 57/50; maturity relative gains 27.63% and 25.85%; W=1531, p=.051"
  "no educational-effect CI or standardized between-group effect size is promoted; p-values on additional motivation/collective-efficacy contrasts remain outcome-specific"
  Cone.derivesBoundedContrast
  "the design pays bounded differences/descriptive gains between the two active scenario conditions"
  Cone.attributesCausalEffect
  "two active scenarios do not identify the effect of digital-sobriety education versus no intervention, and complete-case loss remains material"
  "next causal discriminator would need an estimand-specific control/comparator and an attrition/missingness account; a significant p-value on one sub-outcome cannot pay those predicates"

------------------------------------------------------------------------
-- Green, Molloy & Duggan 2022: randomized design, analysis-local exclusions.
------------------------------------------------------------------------

greenScope : PNF.AssertionScope
greenScope = PNF.assertionScope
  "validated adult volunteer datasets from the randomized factorial study"
  "online sustainability-learning study, predominantly Ireland/UK"
  "system-dynamics simulation exposure"
  "reported analysed control group after Quiz-1 outlier exclusion"
  "immediate sustainability Quiz-1 score"
  "single-session immediate assessment"

greenPredicates : List PNF.PredicateAtom
greenPredicates =
  PNF.predicateAtom "randomized-participant" PNF.populationPredicate "participant × randomized-group"
    "participant belongs to the validated randomized study population"
  ∷ PNF.predicateAtom "simulation-exposure" PNF.interventionPredicate "participant × learning-factor"
    "simulation-group participants receive the simulation factor"
  ∷ PNF.predicateAtom "analysed-control" PNF.comparatorPredicate "simulation-group × control-analysis-set"
    "reported Quiz-1 comparison uses simulation n=24 versus analysed control n=27 after control outlier removal"
  ∷ PNF.predicateAtom "quiz-one-score" PNF.outcomePredicate "participant × immediate-quiz"
    "outcome is immediate measured sustainability Quiz-1 performance"
  ∷ PNF.predicateAtom "reported-association" PNF.significancePredicate "group × quiz-score"
    "simulation M=78.4, SD=14.1 versus analysed control M=71.9, SD=9.3; p=.018 and Cohen's d=.6"
  ∷ PNF.predicateAtom "post-randomization-analysis-change" PNF.contextPredicate "randomized-set × analysed-set"
    "reported inferential analysis excludes a randomized control outlier; later transfer analysis excludes further non-engaged records"
  ∷ []

greenSimulationAssertion : PNF.PredicateNormalAssertion
greenSimulationAssertion = PNF.predicateNormalAssertion
  "green-2022-simulation-quiz-one-association"
  "In the reported analysed contrast, participants exposed to simulation had higher immediate Quiz-1 scores than the analysed control group."
  PNF.studyPopulationQ
  PNF.associationalF
  greenScope
  greenPredicates
  "same-object DOI 10.3390/su14010394; randomized factorial design retained separately from analysis-local post-randomization exclusions"

greenResultAudit : StudyResultAudit
greenResultAudit = study-result-audit
  "green-molloy-duggan-2022-simulation"
  Green.greenMolloyDugganPilotProfile
  greenSimulationAssertion
  "106 validated randomized datasets; full groups 28/26/24/28; reported Quiz-1 simulation n=24 versus analysed control n=27; p=.018; Cohen's d=.6"
  "no numerical effect CI reported; '95% confidence level' language is not converted into CI endpoints"
  Cone.associatesTreatmentAndOutcome
  "randomized assignment plus the analysed contrast strongly supports treatment-outcome association for the measured immediate quiz, but the review keeps analysis-set admissibility separate"
  Cone.attributesCausalEffect
  "post-randomization exclusion changes the comparator analysis set; causal promotion requires an explicit estimand/analysis-set decision rather than inference from the RCT label alone"
  "next proof-search target is not another supporting citation: it is the analysis-set/estimand question—whether the reported exclusion rule is admissible for the declared causal consumer; construct completeness and transport remain separate later obligations"

studyResultAudits : List StudyResultAudit
studyResultAudits =
  iaqResultAudit
  ∷ brasslerResultAudit
  ∷ descampsResultAudit
  ∷ greenResultAudit
  ∷ []

studyResultAssertionCount : Nat
studyResultAssertionCount = 4

studyResultPNFReading : String
studyResultPNFReading =
  "Digital-ESD synthesis now consumes explicit study-result predicates rather than article-level rhetoric. Each audit retains the sampled population, context, intervention/exposure, comparator, measured outcome, time window and inferential force together with n/effect/uncertainty receipts. Proof search starts at the first unpaid implication: Deng needs counterfactual control for causal promotion; Brassler needs both analysis-set recovery and non-random-allocation repair; Descamps needs an estimand-specific control plus missingness account; Green needs an explicit post-randomization analysis-set/estimand decision before causal promotion. More citations cannot substitute for those discriminators."
