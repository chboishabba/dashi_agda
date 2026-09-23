module DASHI.Education.DigitalESDZhaoWhoMissingPNFExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.AttributedSourceCore as Attr
import DASHI.Core.IntersectionalNonFactorability as Factors
import DASHI.Education.DigitalESDDisabilityIntersectionalityAuditExact as Disability
import DASHI.Education.DigitalESDStudyIntersectionalAbsenceAuditExact as Absence
import DASHI.Education.DigitalESDDisabilityStudyPNFExact as DisabilityPNF
import DASHI.Reasoning.PredicateNormalFormEvidenceAuditExact as PNF
import DASHI.Reasoning.ExperimentalAssertionPNFImplicationConeExact as Cone

------------------------------------------------------------------------
-- ZHAO / COX / CHEN: WHO IS NOT AT THE TABLE?
--
-- This is a source-specific refinement of the already-canonical disability PNF
-- audit. It does not create a new disability ontology. It retains the exact
-- attributed DOI source and asks what the 124-response analytic carrier can and
-- cannot say about the larger registered-disabled-student frame and about
-- students whose disability or access needs are not visible to that frame.
------------------------------------------------------------------------

sourceObject : Attr.AttributedSource
sourceObject = Disability.zhaoCoxChenGenAISource

disabilityBoundary : Disability.DisabilityDigitalESDBoundary
disabilityBoundary = Disability.canonicalDisabilityDigitalESDBoundary

registeredDisabledStudentCount : Nat
registeredDisabledStudentCount = 7188

validResponseCount : Nat
validResponseCount = 124

reportedGenAIUserCount : Nat
reportedGenAIUserCount = 96

zhaoWhoMissingScope : PNF.AssertionScope
zhaoWhoMissingScope = PNF.assertionScope
  "7188 registered disabled students were in the university disability-services frame; 124 valid survey responses formed the realised analytic carrier"
  "one UK university"
  "self-directed use/non-use of generative AI for academic writing"
  "respondents versus the unobserved eligible/nonresponding remainder; this is not an experimental comparator"
  "reported uses, barriers, concerns, affordability and policy/training preferences among respondents"
  "survey distributed February-March 2024"

zhaoWhoMissingPredicates : List PNF.PredicateAtom
zhaoWhoMissingPredicates =
  PNF.predicateAtom "registered-disability-frame" PNF.populationPredicate "student × disability-registration"
    "the institution reported 7188 registered students with disabilities in a university population over 30000"
  ∷ PNF.predicateAtom "realised-response-carrier" PNF.populationPredicate "student × valid-response"
    "124 valid responses form the realised analytic carrier"
  ∷ PNF.predicateAtom "self-disclosure-visibility" PNF.contextPredicate "student × disclosure × institutional-registration"
    "visibility depends on disability registration/self-disclosure; the source notes reluctance among some international students to identify as disabled"
  ∷ PNF.predicateAtom "represented-disability-mix" PNF.contextPredicate "respondent × disclosed-condition"
    "respondents were concentrated in neurodiversity, specific learning difficulties and social/communication impairments, with multiple-condition disclosure permitted"
  ∷ PNF.predicateAtom "genai-use-among-respondents" PNF.outcomePredicate "respondent × generative-AI-use"
    "96 of 124 respondents reported generative-AI use"
  ∷ PNF.predicateAtom "policy-voice-among-respondents" PNF.authorityPredicate "respondent × institutional-policy"
    "respondents expressed a desire to participate in institutional generative-AI policymaking"
  ∷ PNF.predicateAtom "nonresponse-characteristics-unobserved" PNF.contextPredicate "eligible-frame × nonresponse"
    "the study does not measure the characteristics, GenAI use or policy preferences of the nonresponding registered-disabled-student remainder"
  ∷ []

zhaoWhoMissingAssertion : PNF.PredicateNormalAssertion
zhaoWhoMissingAssertion = PNF.predicateNormalAssertion
  "zhao-2025-disabled-student-genai-who-missing"
  "Among 124 valid disabled-student respondents from a university with 7188 registered disabled students, generative-AI use, barriers, affordability concerns and policy/training preferences were described; the response set does not itself represent the unobserved eligible/nonresponding remainder."
  PNF.studyPopulationQ
  PNF.descriptiveF
  zhaoWhoMissingScope
  zhaoWhoMissingPredicates
  "same-object DOI 10.1016/j.iheduc.2025.101014; exact publisher Methods/Results retain 7188 registered disabled students, 124 valid responses and 96 respondent GenAI users"

strongestPaidImplication : Cone.ImplicationKind
strongestPaidImplication = Cone.restatesMeasuredResult

strongestPaidReason : String
strongestPaidReason =
  "The source pays descriptive claims about the realised 124-response carrier, including reported use, barriers, concerns and policy/training preferences."

firstUnpaidImplication : Cone.ImplicationKind
firstUnpaidImplication = Cone.transportsPopulation

firstUnpaidReason : String
firstUnpaidReason =
  "The 124-response carrier does not establish prevalence or preference distributions for all 7188 registered disabled students, for disabled students who did not respond, or for disabled students not present in the institutional registration frame."

canonicalZhaoPNFAudit : DisabilityPNF.DisabilityStudyResultAudit
canonicalZhaoPNFAudit = DisabilityPNF.zhaoResultAudit

absenceQuestions : List Absence.AbsenceAuditQuestion
absenceQuestions = Absence.absenceAuditQuestions

------------------------------------------------------------------------
-- Constructive source-shaped collision: the same response count can coexist
-- with different representation adequacy depending on access/disclosure and
-- coverage. Therefore n=124 by itself cannot pay the 'who is missing?' audit.
------------------------------------------------------------------------

data ZhaoRepresentationWorld : Set where
  sameNDisclosureFiltered : ZhaoRepresentationWorld
  sameNAccessAudited : ZhaoRepresentationWorld

data ResponseCountSurface : Set where
  same124Responses : ResponseCountSurface

responseCountProjection : ZhaoRepresentationWorld → ResponseCountSurface
responseCountProjection sameNDisclosureFiltered = same124Responses
responseCountProjection sameNAccessAudited = same124Responses

representationAdequacy : ZhaoRepresentationWorld → Bool
representationAdequacy sameNDisclosureFiltered = false
representationAdequacy sameNAccessAudited = true

representationOutcomesDiffer :
  representationAdequacy sameNDisclosureFiltered ≡
  representationAdequacy sameNAccessAudited → ⊥
representationOutcomesDiffer ()

responseCountWitness :
  Factors.NonFactorabilityWitness responseCountProjection representationAdequacy
responseCountWitness = Factors.nonFactorabilityWitness
  sameNDisclosureFiltered sameNAccessAudited refl representationOutcomesDiffer

responseCountCannotDetermineRepresentationAdequacy :
  Factors.FactorsThrough responseCountProjection representationAdequacy → ⊥
responseCountCannotDetermineRepresentationAdequacy =
  Factors.witnessRulesOutEveryFlatFactorisation responseCountWitness

------------------------------------------------------------------------
-- Promotion firewalls.
------------------------------------------------------------------------

data RegisteredDisabilityFrameEqualsAllDisabledStudents : Set where
data ResponseFractionCreatesPopulationPrevalence : Set where
data NonresponseCreatesKnownExclusionCause : Set where
data DisclosurePatternCreatesDiagnosis : Set where

disabilityRegistrationFrameDoesNotEqualAllDisabledStudents :
  RegisteredDisabilityFrameEqualsAllDisabledStudents → ⊥
disabilityRegistrationFrameDoesNotEqualAllDisabledStudents ()

responseFractionDoesNotCreatePopulationPrevalence :
  ResponseFractionCreatesPopulationPrevalence → ⊥
responseFractionDoesNotCreatePopulationPrevalence ()

nonresponseDoesNotCreateKnownExclusionCause :
  NonresponseCreatesKnownExclusionCause → ⊥
nonresponseDoesNotCreateKnownExclusionCause ()

disclosurePatternDoesNotCreateDiagnosis : DisclosurePatternCreatesDiagnosis → ⊥
disclosurePatternDoesNotCreateDiagnosis ()

zhaoWhoMissingReading : String
zhaoWhoMissingReading =
  "The Zhao/Cox/Chen source is useful precisely because it makes the missing-table problem visible. The university reported 7188 registered disabled students, but the realised survey carrier is 124 valid responses. The study legitimately describes those respondents, including 96 reported GenAI users and a desire for policy participation, while transport to the full registered frame remains unpaid. Registration/self-disclosure is itself a visibility filter, and the source notes reluctance among some international students to identify as disabled. The review therefore retains who responded, who is merely in the institutional frame, who may be absent from that frame, and whose nonresponse characteristics remain unknown without inferring a diagnosis or exclusion cause."
