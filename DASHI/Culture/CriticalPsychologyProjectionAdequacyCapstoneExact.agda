module DASHI.Culture.CriticalPsychologyProjectionAdequacyCapstoneExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

import DASHI.Core.IntersectionalNonFactorability as INF
import DASHI.Core.FeministRechartingSourceBridgeExact as Feminist
import DASHI.Core.CriticalRelationalGrammarCapstoneExact as Critical
import DASHI.Core.TrinhSubjectInMakingNoncollapseExact as Trinh
import DASHI.Culture.LopezRiosPsychologisationDialecticNonDescentExact as Lopez
import DASHI.Culture.LopezRiosSourcePropositionReceiptsExact as LopezReceipts
import DASHI.Culture.MarxLabourUnionSourceBoundaryExact as Marx
import DASHI.Philosophy.MentalHealthWorkedExample as Mental
import DASHI.Philosophy.MentalHealthEvidenceAdapter as MentalEvidence
import DASHI.Promotion.SystemicDistressReframingBoundary as Distress
import DASHI.Reasoning.DevelopmentalAttunementPNFBridge as Developmental
import DASHI.Reasoning.LacanZizekIdeologyBridge as Ideology
import DASHI.Reasoning.LacanCapitalistDiscourseMutation as Capitalist

------------------------------------------------------------------------
-- CRITICAL PSYCHOLOGY PROJECTION ADEQUACY CAPSTONE
--
-- This owner does not define a master psychology or critical-theory ontology.
-- It assembles the already-owned psychology, intersectional, feminist,
-- psychoanalytic, Marxian and source-provenance boundaries around one generic
-- question:
--
--   Does the phenomenon required by a consumer factor through the observation
--   that consumer proposes to use?
--
-- If not, the omitted residual must remain visible.  If a systemic or critical
-- reading is introduced, it still does not automatically establish clinical,
-- empirical, or total causal closure.
------------------------------------------------------------------------

data ExplanatoryFibre : Set where
  bodilyFibre
  developmentalFibre
  relationalFibre
  individualPsychologicalFibre
  symbolicDiscursiveFibre
  ideologicalFibre
  materialLabourFibre
  intersectionalSituatedFibre
  historicalFibre
  : ExplanatoryFibre

data ConsumerKind : Set where
  selfDescriptionConsumer
  clinicalConsumer
  structuralCausalConsumer
  relationalConsumer
  ideologicalConsumer
  materialPoliticalConsumer
  intersectionalConsumer
  historicalConsumer
  : ConsumerKind

data ProjectionJudgement : Set where
  adequateProjection
  residualRequired
  causalClosureBlocked
  authorityPromotionBlocked
  : ProjectionJudgement

record CriticalPsychologyQuery : Set where
  constructor critical-psychology-query
  field
    consumer : ConsumerKind
    observedFibre : ExplanatoryFibre
    targetFibre : ExplanatoryFibre
    purpose : String

open CriticalPsychologyQuery public

canonicalPsychologisationQuery : CriticalPsychologyQuery
canonicalPsychologisationQuery =
  critical-psychology-query
    structuralCausalConsumer
    individualPsychologicalFibre
    materialLabourFibre
    "test whether an individual distress observation is sufficient for the structural dependency required by the causal consumer"

------------------------------------------------------------------------
-- Exact canonical witness: individual observation is too coarse for this
-- structural consumer.
------------------------------------------------------------------------

canonicalPsychologisationNonfactorability :
  INF.NonFactorabilityWitness
    (λ state → Lopez.individualObservation state Lopez.samePerson)
    (λ state → Lopez.structuralDependency state Lopez.samePerson)
canonicalPsychologisationNonfactorability = Lopez.genericPsychologisationWitness

canonicalPsychologicalProjectionIsStructurallyInadequate :
  INF.FactorsThrough
    (λ state → Lopez.individualObservation state Lopez.samePerson)
    (λ state → Lopez.structuralDependency state Lopez.samePerson) →
  ⊥
canonicalPsychologicalProjectionIsStructurallyInadequate =
  Lopez.genericIndividualObserverCannotFactorStructuralDependency

canonicalIndividualRechartingStillInadequate :
  ∀ {Recharted : Set} →
  (rechart : Lopez.IndividualObservation → Recharted) →
  INF.FactorsThrough
    (λ state → rechart (Lopez.individualObservation state Lopez.samePerson))
    (λ state → Lopez.structuralDependency state Lopez.samePerson) →
  ⊥
canonicalIndividualRechartingStillInadequate =
  Lopez.genericIndividualRechartingCannotRecoverStructuralDependency

------------------------------------------------------------------------
-- Positive repair pattern: add information rather than relabeling an erased
-- quotient.  The feminist source bridge owns the generic strict-refinement
-- construction; it is reused here without transferring source authorship.
------------------------------------------------------------------------

positiveResidualRepairPattern :
  Feminist.PositiveRecharting Feminist.inheritedChart
positiveResidualRepairPattern = Feminist.canonicalPositiveRecharting

positiveResidualRepairIsStrict :
  _
positiveResidualRepairIsStrict = Feminist.canonicalPositiveRechartingIsStrict

------------------------------------------------------------------------
-- Existing psychology surfaces remain primary for multi-causal and clinical
-- governance.  Critical/systemic interpretation is not allowed to erase them.
------------------------------------------------------------------------

mentalHealthPluralCarrier : Mental.MentalHealthCase
mentalHealthPluralCarrier = Mental.canonicalMentalHealthCase

mentalHealthPromotionBoundary : MentalEvidence.MentalHealthPromotionBoundary
mentalHealthPromotionBoundary = MentalEvidence.canonicalMentalHealthPromotionBoundary

systemicDistressBoundary : Distress.SystemicDistressBoundary
systemicDistressBoundary = Distress.canonicalSystemicDistressBoundary

developmentalAuthorityBoundary : Developmental.DevelopmentalAttunementAuthorityBoundary
developmentalAuthorityBoundary = Developmental.canonicalDevelopmentalAttunementAuthorityBoundary

------------------------------------------------------------------------
-- Critical-theory surfaces remain comparison/interpretive owners rather than
-- automatic clinical or political-economic authorities.
------------------------------------------------------------------------

criticalGrammarBoundary : Critical.CriticalRelationalGrammarBoundary
criticalGrammarBoundary = Critical.canonicalCriticalRelationalGrammarBoundary

trinhSubjectFormationStillNonfactorable :
  INF.FactorsThrough Trinh.publicCategory Trinh.subjectFormation → ⊥
trinhSubjectFormationStillNonfactorable =
  Trinh.publicCategoryCannotRecoverSubjectFormation

ideologyBoundary : Ideology.LacanZizekIdeologyBoundary
ideologyBoundary = Ideology.canonicalLacanZizekIdeologyBoundary

capitalistDiscourseBoundary : Capitalist.CapitalistDiscourseAuthorityBoundary
capitalistDiscourseBoundary = Capitalist.canonicalCapitalistDiscourseAuthorityBoundary

marxSourceBoundary : Marx.MarxLabourUnionSourceBoundary
marxSourceBoundary = Marx.canonicalMarxLabourUnionSourceBoundary

lopezRiosSourceBoundary : LopezReceipts.LopezRiosSourcePropositionBoundary
lopezRiosSourceBoundary = LopezReceipts.canonicalLopezRiosSourcePropositionBoundary

------------------------------------------------------------------------
-- Two-sided anti-reduction firewall.
------------------------------------------------------------------------

data IndividualDescriptionExhaustsStructuralCause : Set where
data StructuralCritiqueExhaustsClinicalCause : Set where
data LacanianReadingIsClinicalDiagnosis : Set where
data MarxianRelationIsUniqueDistressCause : Set where
data IntersectionalReadingErasesBody : Set where
data FeministRechartingIsJustSignFlip : Set where
data SharedFormalPatternMergesAuthors : Set where

data SourcePropositionBecomesDASHIProof : Set where

individualDescriptionDoesNotExhaustStructuralCause :
  IndividualDescriptionExhaustsStructuralCause → ⊥
individualDescriptionDoesNotExhaustStructuralCause ()

structuralCritiqueDoesNotExhaustClinicalCause :
  StructuralCritiqueExhaustsClinicalCause → ⊥
structuralCritiqueDoesNotExhaustClinicalCause ()

lacanianReadingDoesNotBecomeDiagnosis : LacanianReadingIsClinicalDiagnosis → ⊥
lacanianReadingDoesNotBecomeDiagnosis ()

marxianRelationDoesNotBecomeUniqueDistressCause :
  MarxianRelationIsUniqueDistressCause → ⊥
marxianRelationDoesNotBecomeUniqueDistressCause ()

intersectionalReadingDoesNotEraseBody : IntersectionalReadingErasesBody → ⊥
intersectionalReadingDoesNotEraseBody ()

feministRepairIsNotJustSignFlip : FeministRechartingIsJustSignFlip → ⊥
feministRepairIsNotJustSignFlip ()

sharedPatternDoesNotMergeAuthors : SharedFormalPatternMergesAuthors → ⊥
sharedPatternDoesNotMergeAuthors ()

sourcePropositionDoesNotBecomeDASHIProof : SourcePropositionBecomesDASHIProof → ⊥
sourcePropositionDoesNotBecomeDASHIProof ()

------------------------------------------------------------------------
-- Public capstone receipt.
------------------------------------------------------------------------

record CriticalPsychologyProjectionAdequacyBoundary : Set where
  constructor critical-psychology-projection-adequacy-boundary
  field
    individualProjectionCanLoseStructuralInformation : Bool
    relabellingCollapsedProjectionCanRecoverLostInformation : Bool
    genuineRepairMayRequireAddedResidual : Bool
    criticalSystemicReadingMayRemainLive : Bool
    criticalSystemicReadingAutomaticallyProvesDiagnosis : Bool
    bodilyDevelopmentalRelationalAxesRemainLive : Bool
    lacanianIdeologyReadingAutomaticallyProvesPoliticalEconomy : Bool
    marxianMaterialReadingAutomaticallyProvesPsychologicalCause : Bool
    singleAxisIdentityAutomaticallyRecoversSituatedOutcome : Bool
    sourcePropositionsRemainDistinctFromDASHITheorems : Bool
    sharedFormalPatternMergesHistoricalDoctrines : Bool

canonicalCriticalPsychologyProjectionAdequacyBoundary :
  CriticalPsychologyProjectionAdequacyBoundary
canonicalCriticalPsychologyProjectionAdequacyBoundary =
  critical-psychology-projection-adequacy-boundary
    true
    false
    true
    true
    false
    true
    false
    false
    false
    true
    false
