module DASHI.Reasoning.RelationRepresentationAdequacyExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.ConsumerRelativeMetaphorTransferFitnessExact as Transfer
import DASHI.Cognition.PNF.DynamicMultiQueryMultiResolutionExact as Dynamic
import DASHI.Reasoning.RelationRepresentationSourceRegistryExact as Sources

------------------------------------------------------------------------
-- RELATION REPRESENTATION ADEQUACY
--
-- A fixed offset / latent direction is one candidate representation family,
-- not the primitive.  The generic object separates:
--
--   representation family
--   comparison geometry
--   task-relative consumer factorisation
--   dynamic trace commutation
--   realization/authority (owned by the companion module)
--
-- Static and dynamic adequacy reuse existing repository owners rather than
-- creating a second compression or future-equivalence calculus.
------------------------------------------------------------------------

data TransformationFamily : Set where
  fixedTranslation
  linearRotation
  affineTransformation
  learnedNonlinearTransformation
  quotientCompression
  manifoldConstrainedTransformation
  applicationSuppliedTransformation
  : TransformationFamily

data ComparisonGeometry : Set where
  cosineLikeGeometry
  ordinalConcordanceGeometry
  magnitudeAwareGeometry
  calibratedMonotoneGeometry
  riemannianGeodesicGeometry
  applicationSuppliedGeometry
  : ComparisonGeometry

record SituatedRelationRepresentation
    (State Context Representation RelationCode Similarity : Set) : Set₁ where
  constructor situatedRelationRepresentation
  field
    encode : Context → State → Representation
    relationCode : Context → Representation → Representation → RelationCode
    compareCodes : RelationCode → RelationCode → Similarity
    transformationFamily : TransformationFamily
    comparisonGeometry : ComparisonGeometry
    representationReading : String

open SituatedRelationRepresentation public

------------------------------------------------------------------------
-- Static adequacy is exactly task-relative structural compression.
------------------------------------------------------------------------

record StaticRelationAdequacy
    (Fine Representation Task Output : Set)
    (encodeFine : Fine → Representation)
    (evaluate : Task → Fine → Output) : Set₁ where
  constructor staticRelationAdequacy
  field
    compression :
      Compression.TaskRelativeStructuralCompression
        Fine Representation Task Output encodeFine evaluate
    adequacyReading : String

open StaticRelationAdequacy public

sameRepresentationSameDeclaredConsumerOutput :
  ∀ {Fine Representation Task Output : Set}
    {encodeFine : Fine → Representation}
    {evaluate : Task → Fine → Output} →
  StaticRelationAdequacy Fine Representation Task Output encodeFine evaluate →
  (task : Task) →
  {left right : Fine} →
  encodeFine left ≡ encodeFine right →
  evaluate task left ≡ evaluate task right
sameRepresentationSameDeclaredConsumerOutput adequacy =
  Compression.sameRepresentationSameDeclaredTaskOutput (compression adequacy)

------------------------------------------------------------------------
-- A collision for any richer consumer blocks universal adequacy.
------------------------------------------------------------------------

record ConsumerCollision
    {Fine Representation Output : Set}
    (encodeFine : Fine → Representation)
    (consumer : Fine → Output) : Set where
  constructor consumerCollision
  field
    failure : Compression.CompressionFailureWitness encodeFine consumer
    collisionReading : String

open ConsumerCollision public

consumerCollisionBlocksDescent :
  ∀ {Fine Representation Output : Set}
    {encodeFine : Fine → Representation}
    {consumer : Fine → Output} →
  ConsumerCollision encodeFine consumer →
  NonFactor.FactorsThrough encodeFine consumer →
  ⊥
consumerCollisionBlocksDescent collision =
  Compression.compressionFailureBlocksDescent (failure collision)

------------------------------------------------------------------------
-- Consumer-relative fitness is already the exact positive/negative pair:
-- one declared task factors through the code while a second consumer fails.
------------------------------------------------------------------------

existingConsumerRelativeTransferOwner : String
existingConsumerRelativeTransferOwner =
  "DASHI.Reasoning.ConsumerRelativeMetaphorTransferFitnessExact remains the generic owner for useful-here / insufficient-there representation fitness."

------------------------------------------------------------------------
-- Dynamic adequacy reuses the PNF dynamic multi-query owner.  The retained
-- representation is not future-safe merely because it works at the current
-- state: both coarse and residual coordinates must commute with every declared
-- query/action step.
------------------------------------------------------------------------

record FutureSafeRelationAdequacy
    (Fine Coarse Local Query Observation : Set) : Set₁ where
  constructor futureSafeRelationAdequacy
  field
    dynamicSystem :
      Dynamic.DynamicMultiResolutionSystem
        Fine Coarse Local Query Observation
    family : TransformationFamily
    geometry : ComparisonGeometry
    futureSafetyReading : String

open FutureSafeRelationAdequacy public

sameRetainedRelationStateGivesSameObservationAfterEveryTrace :
  ∀ {Fine Coarse Local Query Observation : Set}
    (adequacy : FutureSafeRelationAdequacy Fine Coarse Local Query Observation)
    {left right : Fine} →
  Dynamic.compressGlobal (dynamicSystem adequacy) left
    ≡ Dynamic.compressGlobal (dynamicSystem adequacy) right →
  Dynamic.localResidual (dynamicSystem adequacy) left
    ≡ Dynamic.localResidual (dynamicSystem adequacy) right →
  (queries : List Query) →
  Dynamic.observeFine (dynamicSystem adequacy)
      (Dynamic.runFine (dynamicSystem adequacy) queries left)
    ≡ Dynamic.observeFine (dynamicSystem adequacy)
      (Dynamic.runFine (dynamicSystem adequacy) queries right)
sameRetainedRelationStateGivesSameObservationAfterEveryTrace adequacy =
  Dynamic.sameInitialRetainedCarrierImpliesSameObservationAfterEveryQueryTrace
    (dynamicSystem adequacy)

relationRepresentationCommutesWithEveryDeclaredTrace :
  ∀ {Fine Coarse Local Query Observation : Set}
    (adequacy : FutureSafeRelationAdequacy Fine Coarse Local Query Observation)
    (queries : List Query)
    (fine : Fine) →
  Dynamic.compressGlobal (dynamicSystem adequacy)
      (Dynamic.runFine (dynamicSystem adequacy) queries fine)
    ≡ Dynamic.runCoarse (dynamicSystem adequacy) queries
      (Dynamic.compressGlobal (dynamicSystem adequacy) fine)
relationRepresentationCommutesWithEveryDeclaredTrace adequacy =
  Dynamic.compressCommutesWithEveryQueryTrace (dynamicSystem adequacy)

relationResidualCommutesWithEveryDeclaredTrace :
  ∀ {Fine Coarse Local Query Observation : Set}
    (adequacy : FutureSafeRelationAdequacy Fine Coarse Local Query Observation)
    (queries : List Query)
    (fine : Fine) →
  Dynamic.localResidual (dynamicSystem adequacy)
      (Dynamic.runFine (dynamicSystem adequacy) queries fine)
    ≡ Dynamic.runLocal (dynamicSystem adequacy) queries
      (Dynamic.localResidual (dynamicSystem adequacy) fine)
relationResidualCommutesWithEveryDeclaredTrace adequacy =
  Dynamic.localResidualCommutesWithEveryQueryTrace (dynamicSystem adequacy)

------------------------------------------------------------------------
-- Geometry and metric are separate coordinates from representation family.
------------------------------------------------------------------------

data SameRepresentationDifferentComparisonPermission : Set where

data BestSimilarityImpliesSemanticRealizationPermission : Set where

data StaticAdequacyImpliesFutureSafetyPermission : Set where

bestSimilarityCannotAutoRealizeSemantics :
  BestSimilarityImpliesSemanticRealizationPermission → ⊥
bestSimilarityCannotAutoRealizeSemantics ()

staticAdequacyCannotAutoPromoteFutureSafety :
  StaticAdequacyImpliesFutureSafetyPermission → ⊥
staticAdequacyCannotAutoPromoteFutureSafety ()

------------------------------------------------------------------------
-- Concrete bookkeeping specimen: the same transformation family may be paired
-- with different comparison geometries.  This is a typing result, not a claim
-- that any metric is empirically superior in every task.
------------------------------------------------------------------------

data DemoState : Set where demoLeft demoRight : DemoState

data DemoContext : Set where demoContext : DemoContext

data DemoRepresentation : Set where demoA demoB : DemoRepresentation

data DemoRelationCode : Set where demoRelation : DemoRelationCode

data DemoSimilarity : Set where cosineScore ordinalScore : DemoSimilarity

demoEncode : DemoContext → DemoState → DemoRepresentation
demoEncode demoContext demoLeft = demoA
demoEncode demoContext demoRight = demoB

demoRelationCode :
  DemoContext → DemoRepresentation → DemoRepresentation → DemoRelationCode
demoRelationCode _ _ _ = demoRelation

cosineComparison : DemoRelationCode → DemoRelationCode → DemoSimilarity
cosineComparison _ _ = cosineScore

ordinalComparison : DemoRelationCode → DemoRelationCode → DemoSimilarity
ordinalComparison _ _ = ordinalScore

translationCosineRepresentation :
  SituatedRelationRepresentation
    DemoState DemoContext DemoRepresentation DemoRelationCode DemoSimilarity
translationCosineRepresentation =
  situatedRelationRepresentation
    demoEncode demoRelationCode cosineComparison
    fixedTranslation cosineLikeGeometry
    "A fixed translation candidate evaluated under a cosine-like comparison geometry."

translationOrdinalRepresentation :
  SituatedRelationRepresentation
    DemoState DemoContext DemoRepresentation DemoRelationCode DemoSimilarity
translationOrdinalRepresentation =
  situatedRelationRepresentation
    demoEncode demoRelationCode ordinalComparison
    fixedTranslation ordinalConcordanceGeometry
    "The same representation family evaluated under an ordinal-concordance comparison geometry."

record RelationRepresentationAdequacyBoundary : Set where
  constructor relationRepresentationAdequacyBoundary
  field
    fixedTranslationIsUniversalPrimitive : Bool
    fixedTranslationIsUniversalPrimitiveIsFalse :
      fixedTranslationIsUniversalPrimitive ≡ false

    representationDeterminesComparisonGeometry : Bool
    representationDeterminesComparisonGeometryIsFalse :
      representationDeterminesComparisonGeometry ≡ false

    similarityMetricDeterminesSemanticInterpretation : Bool
    similarityMetricDeterminesSemanticInterpretationIsFalse :
      similarityMetricDeterminesSemanticInterpretation ≡ false

    staticTaskFactorisationImpliesDynamicTraceSafety : Bool
    staticTaskFactorisationImpliesDynamicTraceSafetyIsFalse :
      staticTaskFactorisationImpliesDynamicTraceSafety ≡ false

    oneConsumerFactorisationImpliesUniversalSufficiency : Bool
    oneConsumerFactorisationImpliesUniversalSufficiencyIsFalse :
      oneConsumerFactorisationImpliesUniversalSufficiency ≡ false

    dynamicTraceCommutationIsExplicitlyRepresentable : Bool
    dynamicTraceCommutationIsExplicitlyRepresentableIsTrue :
      dynamicTraceCommutationIsExplicitlyRepresentable ≡ true

canonicalRelationRepresentationAdequacyBoundary :
  RelationRepresentationAdequacyBoundary
canonicalRelationRepresentationAdequacyBoundary =
  relationRepresentationAdequacyBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl

sourceBoundary : Sources.RelationRepresentationAttributionBoundary
sourceBoundary = Sources.canonicalRelationRepresentationAttributionBoundary
