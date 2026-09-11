module DASHI.Reasoning.FibreRoutingDistillationCompressionCrossPollinationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Reasoning.FibreRoutingJoinedObserverAdequacyExact as Joined
import DASHI.Core.QueryIndexedProjectionAdequacyExact as Query
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationRealizationExact as Realization

------------------------------------------------------------------------
-- DISTILLATION / PRUNING / QUANTIZATION / LOW-RANK / EXPERT-MERGE WELD
--
-- These techniques are not identified with one another.  They share only the
-- consumer-relative compression grammar:
--
--   rich/source carrier -> compressed/deployment carrier -> declared consumer.
--
-- A compression is adequate exactly for consumers that still factor through
-- the compressed carrier.  Agreement on one teacher/output surface does not
-- imply mechanism recovery, future-safe adequacy, or adequacy for another
-- consumer.
------------------------------------------------------------------------

data CompressionTechnique : Set where
  knowledgeDistillation : CompressionTechnique
  structuredPruning : CompressionTechnique
  unstructuredPruning : CompressionTechnique
  quantization : CompressionTechnique
  lowRankFactorization : CompressionTechnique
  adapterBottleneck : CompressionTechnique
  expertMerging : CompressionTechnique
  sparseExpertRouting : CompressionTechnique
  representationBottleneck : CompressionTechnique

data DistillationTarget : Set where
  outputDistributionTarget : DistillationTarget
  intermediateFeatureTarget : DistillationTarget
  relationTarget : DistillationTarget
  routingTarget : DistillationTarget
  multiTarget : DistillationTarget

record CompressionTechniqueProfile : Set where
  constructor compressionTechniqueProfile
  field
    technique : CompressionTechnique
    changesParameterCarrier : Bool
    changesNumericPrecision : Bool
    changesActiveFibreSet : Bool
    mayUseTeacherSignal : Bool
    reading : String

open CompressionTechniqueProfile public

knowledgeDistillationProfile : CompressionTechniqueProfile
knowledgeDistillationProfile =
  compressionTechniqueProfile
    knowledgeDistillation true false false true
    "Student is trained against a teacher-derived target; matching that target is consumer-relative and does not identify teacher mechanism."

pruningProfile : CompressionTechniqueProfile
pruningProfile =
  compressionTechniqueProfile
    structuredPruning true false true false
    "Parameters/fibres are removed; any erased distinction remains a typed adequacy debt for consumers that need it."

quantizationProfile : CompressionTechniqueProfile
quantizationProfile =
  compressionTechniqueProfile
    quantization false true false false
    "Numeric carrier is coarsened; acceptability is indexed by the downstream consumer rather than precision alone."

lowRankProfile : CompressionTechniqueProfile
lowRankProfile =
  compressionTechniqueProfile
    lowRankFactorization true false false false
    "A lower-dimensional factorization is useful only for consumers whose answers descend through that factorization."

expertMergeProfile : CompressionTechniqueProfile
expertMergeProfile =
  compressionTechniqueProfile
    expertMerging true false true false
    "Distinct experts may be merged only when the declared consumer does not require the distinction between their fibres."

sparseRoutingProfile : CompressionTechniqueProfile
sparseRoutingProfile =
  compressionTechniqueProfile
    sparseExpertRouting false false true false
    "Only a context-selected expert subset is active; sparsity itself is not an adequacy theorem."

------------------------------------------------------------------------
-- Finite teacher/student specimen.
--
-- Two teacher states have the same coarse answer but different rich relational
-- answers.  A student that collapses them can therefore be perfectly adequate
-- for the coarse consumer while provably inadequate for the rich consumer.
------------------------------------------------------------------------

data TeacherState : Set where
  teacherStateA : TeacherState
  teacherStateB : TeacherState

data StudentState : Set where
  distilledState : StudentState

data CoarseTeacherAnswer : Set where
  sameCoarseAnswer : CoarseTeacherAnswer

data RichTeacherAnswer : Set where
  richAnswerA : RichTeacherAnswer
  richAnswerB : RichTeacherAnswer

data DistillationQuery : Set where
  coarseTeacherQuery : DistillationQuery
  richRelationQuery : DistillationQuery

data DistillationAnswer : Set where
  coarseAnswer : CoarseTeacherAnswer → DistillationAnswer
  richAnswer : RichTeacherAnswer → DistillationAnswer

studentProjection : TeacherState → StudentState
studentProjection teacherStateA = distilledState
studentProjection teacherStateB = distilledState

coarseTeacherConsumer : TeacherState → CoarseTeacherAnswer
coarseTeacherConsumer teacherStateA = sameCoarseAnswer
coarseTeacherConsumer teacherStateB = sameCoarseAnswer

richTeacherConsumer : TeacherState → RichTeacherAnswer
richTeacherConsumer teacherStateA = richAnswerA
richTeacherConsumer teacherStateB = richAnswerB

distillationAnswer : DistillationQuery → TeacherState → DistillationAnswer
distillationAnswer coarseTeacherQuery state = coarseAnswer (coarseTeacherConsumer state)
distillationAnswer richRelationQuery state = richAnswer (richTeacherConsumer state)

distillationSemantics :
  Query.QuerySemantics TeacherState DistillationQuery DistillationAnswer
distillationSemantics = Query.querySemantics distillationAnswer

studentAdequateForCoarseTeacherOutput :
  Query.AdequateFor studentProjection distillationSemantics coarseTeacherQuery
studentAdequateForCoarseTeacherOutput =
  Query.factorsForQuery
    (λ _ → coarseAnswer sameCoarseAnswer)
    (λ state → refl)

studentRichRelationDefect :
  Query.QueryAdequacyDefect studentProjection distillationSemantics richRelationQuery
studentRichRelationDefect =
  Query.queryAdequacyDefect teacherStateA teacherStateB refl (λ ())

studentCannotAnswerRichRelationQuery :
  Query.AdequateFor studentProjection distillationSemantics richRelationQuery → ⊥
studentCannotAnswerRichRelationQuery =
  Query.queryAdequacyDefectBlocksFactorisation studentRichRelationDefect

studentCompressionFailure :
  Compression.CompressionFailureWitness studentProjection richTeacherConsumer
studentCompressionFailure =
  Compression.compressionFailureWitness
    teacherStateA teacherStateB refl (λ ())

studentCannotRealizeRichTeacherMechanism :
  Realization.RepresentationRealizationWitness
    studentProjection richTeacherConsumer → ⊥
studentCannotRealizeRichTeacherMechanism =
  Realization.representationCollisionBlocksRealization studentCompressionFailure

------------------------------------------------------------------------
-- Joined repair: preserve the distilled state and reattach only the missing
-- relational fibre.  This mirrors the Fly hard+overlap repair and keeps the
-- smaller representation as a valid coordinate rather than discarding it.
------------------------------------------------------------------------

studentPlusRichFibre : TeacherState → StudentState × RichTeacherAnswer
studentPlusRichFibre = Joined.joinObserver studentProjection richTeacherConsumer

joinedStudentAdequateForRichRelation :
  Query.AdequateFor studentPlusRichFibre distillationSemantics richRelationQuery
joinedStudentAdequateForRichRelation =
  Query.factorsForQuery
    (λ joined → richAnswer (proj₂ joined))
    (λ state → refl)

------------------------------------------------------------------------
-- Shared technique boundary.
------------------------------------------------------------------------

record DistillationCompressionBoundary : Set where
  constructor distillationCompressionBoundary
  field
    matchingTeacherOutputsImpliesMatchingTeacherMechanism : Bool
    matchingTeacherOutputsImpliesMatchingTeacherMechanismIsFalse :
      matchingTeacherOutputsImpliesMatchingTeacherMechanism ≡ false

    lowerParameterCountImpliesConsumerAdequacy : Bool
    lowerParameterCountImpliesConsumerAdequacyIsFalse :
      lowerParameterCountImpliesConsumerAdequacy ≡ false

    lowerPrecisionImpliesConsumerAdequacy : Bool
    lowerPrecisionImpliesConsumerAdequacyIsFalse :
      lowerPrecisionImpliesConsumerAdequacy ≡ false

    expertMergeRequiresConsumerIndistinguishability : Bool
    expertMergeRequiresConsumerIndistinguishabilityIsTrue :
      expertMergeRequiresConsumerIndistinguishability ≡ true

    sparseRoutingRequiresConsumerAdequacyTest : Bool
    sparseRoutingRequiresConsumerAdequacyTestIsTrue :
      sparseRoutingRequiresConsumerAdequacyTest ≡ true

    lowRankCompressionRequiresConsumerAdequacyTest : Bool
    lowRankCompressionRequiresConsumerAdequacyTestIsTrue :
      lowRankCompressionRequiresConsumerAdequacyTest ≡ true

    oneDistillationTargetImpliesAllConsumerTargets : Bool
    oneDistillationTargetImpliesAllConsumerTargetsIsFalse :
      oneDistillationTargetImpliesAllConsumerTargets ≡ false

    failedCompressedCarrierMayBeLocallyRepairedByMissingFibre : Bool
    failedCompressedCarrierMayBeLocallyRepairedByMissingFibreIsTrue :
      failedCompressedCarrierMayBeLocallyRepairedByMissingFibre ≡ true

    successfulDistillationImpliesFutureSafeGeneralization : Bool
    successfulDistillationImpliesFutureSafeGeneralizationIsFalse :
      successfulDistillationImpliesFutureSafeGeneralization ≡ false

    successfulDistillationImpliesBiologicalMechanismIdentity : Bool
    successfulDistillationImpliesBiologicalMechanismIdentityIsFalse :
      successfulDistillationImpliesBiologicalMechanismIdentity ≡ false

canonicalDistillationCompressionBoundary : DistillationCompressionBoundary
canonicalDistillationCompressionBoundary =
  distillationCompressionBoundary
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
