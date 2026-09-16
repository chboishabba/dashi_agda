module DASHI.Education.DigitalESDStudyResultPNFImplicationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Education.DigitalESDQuantitativeUncertaintyAcquisitionExact as Deng
import DASHI.Education.DigitalESDSourceAttributionCorrectionExact as Correction
import DASHI.Education.DigitalESDAcquisitionSnowballParetoExact as Acquisition
import DASHI.Education.DigitalESDRandomizedCausalAcquisitionExact as Green

------------------------------------------------------------------------
-- STUDY RESULT -> PNF -> DESIGN/STATISTICS -> IMPLICATION
--
-- These are bounded assertions that the current extraction actually pays. A
-- paper's discussion/conclusion may state something stronger; promotion from a
-- paid PNF assertion to a stronger causal, transport or normative assertion
-- requires a new evidence receipt under PredicateNormalFormEvidenceAuditExact.
------------------------------------------------------------------------

record StudyResultPNFAudit : Set where
  constructor study-result-pnf-audit
  field
    source : Attr.AttributedSource
    paidAssertion : PNF.PredicateNormalAssertion
    designReceiptReference : String
    statisticalReceiptReference : String
    uncertaintyReference : String
    intersectionalAbsenceReference : String
    materialEnvironmentalReference : String
    unresolvedPromotionReference : String

open StudyResultPNFAudit public

------------------------------------------------------------------------
-- Deng et al. 2026: one-group paired gain with genuine 95% CI.
------------------------------------------------------------------------

dengScope : PNF.AssertionScope
dengScope = PNF.assertionScope
  "1408 Grades 5-10 students across Sri Lanka, Nepal, Malaysia, Indonesia and Guangxi (China)"
  "multi-region STEM-based indoor-air-quality education program"
  "program exposure"
  "same students pre-test versus post-test; no untreated comparison group"
  "IAQ knowledge score on a 0-100 scale"
  "immediate pre/post"

dengPredicates : List PNF.PredicateAtom
dengPredicates =
  PNF.predicateAtom "sampled-students" PNF.populationPredicate "student × region"
    "the reported paired-gain analysis concerns the 1408 sampled students"
  ∷ PNF.predicateAtom "received-program" PNF.interventionPredicate "student × program"
    "analysed students received the STEM-based IAQ education program"
  ∷ PNF.predicateAtom "paired-knowledge-gain" PNF.outcomePredicate "student × knowledge-score × time"
    "the observed mean post-minus-pre knowledge gain is +9.25 points"
  ∷ PNF.predicateAtom "gain-interval" PNF.significancePredicate "paired-mean-gain"
    "the source reports 95% CI [7.58,10.92], p=2.30e-26 and Cohen's dz=.289 for the observed paired gain"
  ∷ PNF.predicateAtom "no-counterfactual-control" PNF.comparatorPredicate "study design"
    "there is no untreated/non-intervention comparison group, so the paired gain is not a counterfactual treatment effect"
  ∷ []

dengPaidAssertion : PNF.PredicateNormalAssertion
dengPaidAssertion = PNF.predicateNormalAssertion
  "deng-2026-paid-paired-gain"
  "In the sampled five-region student cohorts, the reported immediate post-program IAQ knowledge score exceeded the pre-program score by a mean 9.25 points (95% CI [7.58,10.92], dz=.289)."
  PNF.studyPopulationQ
  PNF.comparativeF
  dengScope
  dengPredicates
  "exact primary source DOI 10.3390/su18147165; same-object effect/CI extraction retained in DigitalESDQuantitativeUncertaintyAcquisitionExact"

------------------------------------------------------------------------
-- Braßler 2024: quasi-experimental time×group contrast, effect size, no CI.
------------------------------------------------------------------------

brasslerScope : PNF.AssertionScope
brasslerScope = PNF.assertionScope
  "reported study sample N=409 University of Hamburg students; inferential analysis denominator unresolved"
  "one-semester OER-production course and same-cohort comparison seminars"
  "OER production course"
  "same-cohort discipline seminars unrelated to OER content development"
  "self-reported digital competence / Creative Internet Skills Scale"
  "pre-course to post-course within one semester"

brasslerPredicates : List PNF.PredicateAtom
brasslerPredicates =
  PNF.predicateAtom "oer-course-group" PNF.interventionPredicate "student × course"
    "the focal group participated in the OER-production course"
  ∷ PNF.predicateAtom "comparison-group" PNF.comparatorPredicate "student × course"
    "the comparison group took same-cohort discipline seminars unrelated to OER production"
  ∷ PNF.predicateAtom "time-by-group-change" PNF.outcomePredicate "group × time × digital-competence-score"
    "digital-competence scores increased more over time in the OER-production group than in the comparison group"
  ∷ PNF.predicateAtom "reported-model-effect" PNF.significancePredicate "repeated-measures-model"
    "the source reports Time×Group F(1,191)=22.4, p<.001, partial eta-squared=.105"
  ∷ PNF.predicateAtom "nonrandom-self-selection" PNF.contextPredicate "study design"
    "allocation was not reported as randomized and the source acknowledges group-equivalence/self-selection threats"
  ∷ []

brasslerPaidAssertion : PNF.PredicateNormalAssertion
brasslerPaidAssertion = PNF.predicateNormalAssertion
  "brassler-2024-paid-time-group-contrast"
  "In the reported quasi-experimental study, self-reported digital competence increased more over the semester in the OER-production group than in the comparison group (Time×Group F(1,191)=22.4, p<.001, partial eta-squared=.105)."
  PNF.studyPopulationQ
  PNF.comparativeF
  brasslerScope
  brasslerPredicates
  "exact primary DOI 10.3390/su16041674; analysis-n discrepancy and no effect CI retained rather than reconstructed"

------------------------------------------------------------------------
-- Descamps et al. 2025: two active scenario groups; bounded contrasts only.
------------------------------------------------------------------------

descampsScope : PNF.AssertionScope
descampsScope = PNF.assertionScope
  "164 first-year students attended; 107 complete pre/post cases analysed"
  "University of Mons digital-sobriety learning intervention"
  "individual-action or collective-action charter scenario"
  "active scenario group versus active scenario group; no untreated control"
  "digital-sobriety maturity, motivation and collective-efficacy responses"
  "immediate pre/post learning session"

descampsPredicates : List PNF.PredicateAtom
descampsPredicates =
  PNF.predicateAtom "complete-case-analysis" PNF.populationPredicate "student × measurement-completeness"
    "the primary analysis uses 107 complete pre/post cases from 164 session participants"
  ∷ PNF.predicateAtom "scenario-allocation" PNF.interventionPredicate "student × scenario"
    "students were reported as randomly divided between individual-action and collective-action scenarios"
  ∷ PNF.predicateAtom "maturity-gain" PNF.outcomePredicate "group × digital-sobriety-maturity"
    "reported relative maturity gains are 27.63% and 25.85%"
  ∷ PNF.predicateAtom "scenario-contrast" PNF.significancePredicate "active-group-contrast"
    "the maturity group contrast is W=1531, p=.051; other motivation/collective-efficacy contrasts include p=.038, p=.015 and p<.001"
  ∷ PNF.predicateAtom "no-untreated-control" PNF.comparatorPredicate "study design"
    "both scenario groups received the broader learning intervention, so no untreated counterfactual comparison is available"
  ∷ []

descampsPaidAssertion : PNF.PredicateNormalAssertion
descampsPaidAssertion = PNF.predicateNormalAssertion
  "descamps-2025-paid-active-scenario-contrasts"
  "Among the 107 complete pre/post cases, both digital-sobriety scenario groups showed reported maturity gains, while selected between-scenario motivation/collective-efficacy contrasts differed under the reported non-parametric tests."
  PNF.studyPopulationQ
  PNF.comparativeF
  descampsScope
  descampsPredicates
  "exact primary DOI 10.1186/s41239-025-00569-3; complete-case loss, active-only comparator and missing effect CI retained"

------------------------------------------------------------------------
-- Green, Molloy & Duggan 2022: randomized design, but paid assertion remains
-- associational at the current extraction because reported contrasts use
-- post-randomization exclusions/outlier handling.
------------------------------------------------------------------------

greenScope : PNF.AssertionScope
greenScope = PNF.assertionScope
  "106 validated randomized participant datasets; analysis-local group n differs after exclusions"
  "online 2x2 factorial sustainability-learning trial"
  "system-dynamics simulation exposure"
  "reported analysed control group"
  "immediate sustainability Quiz-1 score"
  "single-session immediate outcome"

greenPredicates : List PNF.PredicateAtom
greenPredicates =
  PNF.predicateAtom "randomized-factorial-assignment" PNF.interventionPredicate "participant × factorial-group"
    "106 validated datasets were randomly assigned across four factorial groups"
  ∷ PNF.predicateAtom "analysis-local-exclusion" PNF.contextPredicate "participant × analysed-set"
    "the focal reported contrast excludes a randomized control outlier, so analysed-set identity differs from the full randomized set"
  ∷ PNF.predicateAtom "simulation-control-score-difference" PNF.outcomePredicate "simulation-group × control-group × quiz-score"
    "reported analysed means are 78.4 versus 71.9 for simulation versus control"
  ∷ PNF.predicateAtom "reported-contrast-effect" PNF.significancePredicate "analysed-contrast"
    "the source reports p=.018 and Cohen's d=.6 for the analysed immediate Quiz-1 simulation/control contrast"
  ∷ PNF.predicateAtom "causal-promotion-residual" PNF.causalPredicate "randomized-assignment × analysed-set × outcome"
    "full causal promotion remains unresolved in this review because post-randomization exclusion handling must be justified for the declared estimand"
  ∷ []

greenPaidAssertion : PNF.PredicateNormalAssertion
greenPaidAssertion = PNF.predicateNormalAssertion
  "green-2022-paid-randomized-analysis-association"
  "In the reported analysed contrast of the randomized trial, simulation exposure was associated with a higher immediate sustainability Quiz-1 score than the analysed control group (d=.6, p=.018); this review does not yet promote that analysed contrast to a fully paid causal assertion."
  PNF.studyPopulationQ
  PNF.associationalF
  greenScope
  greenPredicates
  "exact primary DOI 10.3390/su14010394; randomized assignment retained, post-randomization exclusion/estimand residual retained"

------------------------------------------------------------------------
-- Combined audits. Each paid PNF carries its own statistics and residuals;
-- intersectional/material overlays are mandatory downstream questions rather
-- than silently inferred from the study's reported sample or outcome.
------------------------------------------------------------------------

dengAudit : StudyResultPNFAudit
dengAudit = study-result-pnf-audit
  Deng.iaqSustainabilityEducationSource dengPaidAssertion
  "one-group paired pre/post design; no untreated comparison"
  "n=1408; mean gain +9.25; dz=.289; regional heterogeneity eta-squared=.070"
  "95% CI [7.58,10.92] belongs to the observed paired mean-gain estimand"
  "audit disability/access, geography, language, socioeconomic selection, nonparticipants and regional representation before transport"
  "audit device/platform/compute assumptions if the intervention is promoted as a digital sustainability exemplar"
  "causal treatment effect, delayed learning, behaviour and population transport remain unpaid"

brasslerAudit : StudyResultPNFAudit
brasslerAudit = study-result-pnf-audit
  Correction.brasslerOERESDPublisherSpellingSource
  brasslerPaidAssertion
  "quasi-experimental self-selected groups; same-cohort comparator"
  "reported N=409; Time×Group F(1,191)=22.4; p<.001; partial eta-squared=.105"
  "no educational-effect CI reported; analysis denominator unresolved"
  "audit who can enrol in OER-production work, disability/access needs, discipline mix, language and workload/care constraints"
  "audit platform/device/OER hosting, openness, repair/reuse and infrastructure burden separately from pedagogical outcome"
  "causal effect, analysis-n reconstruction, objective skill performance and transport remain unpaid"

descampsAudit : StudyResultPNFAudit
descampsAudit = study-result-pnf-audit
  Acquisition.descampsDigitalSobrietySource descampsPaidAssertion
  "random division between two active scenarios; no untreated control; complete-case analysis"
  "164 attended; 107 analysed; relative gains 27.63%/25.85%; reported Mann-Whitney p-values"
  "no standardized between-group effect CI reported"
  "audit who is lost in the 164→107 complete-case transition and which disability/access/time/language conditions shape missingness"
  "digital-sobriety content itself requires device/material/energy lifecycle audit rather than treating behaviour instruction as the whole environmental system"
  "causal intervention effect, missingness ignorability, long-term persistence and transport remain unpaid"

greenAudit : StudyResultPNFAudit
greenAudit = study-result-pnf-audit
  Green.greenMolloyDugganSource greenPaidAssertion
  "randomized 2x2 factorial design with analysis-local post-randomization exclusions"
  "106 validated randomized datasets; focal analysed contrast n=24 vs 27; p=.018; d=.6"
  "no numerical CI endpoint for d or mean difference in the source"
  "audit volunteer recruitment 227→106, age/education composition, disability/access, digital confidence and who is filtered by completion/analytics"
  "simulation delivery requires separate compute/device/material footprint if used to argue digital sustainability"
  "causal promotion for the analysed estimand, construct completeness, delayed learning and population transport remain unpaid"

quantitativeResultAudits : List StudyResultPNFAudit
quantitativeResultAudits = dengAudit ∷ brasslerAudit ∷ descampsAudit ∷ greenAudit ∷ []

quantitativeResultAuditCount : Nat
quantitativeResultAuditCount = 4

resultPNFReading : String
resultPNFReading =
  "Each study result is represented as the strongest currently paid Predicate Normal Form assertion: explicit population/context/intervention/comparator/outcome/time predicates, source-local n/effect/CI or significance receipts, and named residual promotions. The paid PNF may be weaker than the paper's discussion rhetoric. Intersectional absence and material/environmental audits are then applied to the paid assertion rather than inferred from citation presence or sample size."
