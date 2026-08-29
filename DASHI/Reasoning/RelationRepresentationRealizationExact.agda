module DASHI.Reasoning.RelationRepresentationRealizationExact where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)

import DASHI.Core.IntersectionalNonFactorability as NonFactor
import DASHI.Reasoning.StructuralMetaphorTaskCompressionExact as Compression
import DASHI.Reasoning.RelationRepresentationAdequacyExact as Adequacy

------------------------------------------------------------------------
-- REPRESENTATION / REALIZATION SEPARATION
--
-- Constructing an embedding/code and constructing a target-domain phenomenon
-- do not by themselves identify their carriers.  A realization is an explicit
-- application-supplied commuting-square witness.  This is the semantic analogue
-- of the repository's fail-closed physical-realization boundaries: arbitrary
-- encodings are not promoted into identity merely because they are convenient.
------------------------------------------------------------------------

record RepresentationRealizationWitness
    {Fine Representation Target : Set}
    (encode : Fine → Representation)
    (targetPhenomenon : Fine → Target) : Set₁ where
  constructor representationRealizationWitness
  field
    realize : Representation → Target
    realizationCommutes :
      (fine : Fine) →
      targetPhenomenon fine ≡ realize (encode fine)
    realizationJustification : String

open RepresentationRealizationWitness public

realizationWitnessYieldsFactorisation :
  ∀ {Fine Representation Target : Set}
    {encode : Fine → Representation}
    {targetPhenomenon : Fine → Target} →
  RepresentationRealizationWitness encode targetPhenomenon →
  NonFactor.FactorsThrough encode targetPhenomenon
realizationWitnessYieldsFactorisation witness =
  NonFactor.factorsThrough
    (realize witness)
    (realizationCommutes witness)

------------------------------------------------------------------------
-- The negative dual: a single collision rules out every realization decoder.
------------------------------------------------------------------------

representationCollisionBlocksRealization :
  ∀ {Fine Representation Target : Set}
    {encode : Fine → Representation}
    {targetPhenomenon : Fine → Target} →
  Compression.CompressionFailureWitness encode targetPhenomenon →
  RepresentationRealizationWitness encode targetPhenomenon →
  ⊥
representationCollisionBlocksRealization collision witness =
  Compression.compressionFailureBlocksDescent collision
    (realizationWitnessYieldsFactorisation witness)

------------------------------------------------------------------------
-- Three layers kept distinct:
--   1. static/task adequacy,
--   2. dynamic/future-safe adequacy,
--   3. target-domain realization.
------------------------------------------------------------------------

record StaticAndRealizedRelation
    (Fine Representation Task Output Target : Set)
    (encode : Fine → Representation)
    (evaluate : Task → Fine → Output)
    (targetPhenomenon : Fine → Target) : Set₁ where
  constructor staticAndRealizedRelation
  field
    staticAdequacy :
      Adequacy.StaticRelationAdequacy
        Fine Representation Task Output encode evaluate
    realization :
      RepresentationRealizationWitness encode targetPhenomenon
    bridgeReading : String

open StaticAndRealizedRelation public

------------------------------------------------------------------------
-- No-promotion permissions are intentionally uninhabited.  A downstream
-- application must supply the realization witness rather than deriving it from
-- fit, geometry, compression, or dynamic commutation alone.
------------------------------------------------------------------------

data StaticAdequacyImpliesRealizationPermission : Set where

data DynamicAdequacyImpliesRealizationPermission : Set where

data GoodGeometryImpliesRealizationPermission : Set where

data RealizationImpliesNormativeAuthorityPermission : Set where

staticAdequacyCannotAutoRealize :
  StaticAdequacyImpliesRealizationPermission → ⊥
staticAdequacyCannotAutoRealize ()

dynamicAdequacyCannotAutoRealize :
  DynamicAdequacyImpliesRealizationPermission → ⊥
dynamicAdequacyCannotAutoRealize ()

goodGeometryCannotAutoRealize :
  GoodGeometryImpliesRealizationPermission → ⊥
goodGeometryCannotAutoRealize ()

realizationCannotAutoPromoteNormativeAuthority :
  RealizationImpliesNormativeAuthorityPermission → ⊥
realizationCannotAutoPromoteNormativeAuthority ()

------------------------------------------------------------------------
-- Concrete property-code witness inspired by the relation-decoder boundary.
-- The same coarse code can be useful while failing to realize a richer target
-- relation.  This is a synthetic DASHI witness, not a reproduction of any
-- empirical LLM experiment.
------------------------------------------------------------------------

data FineRelation : Set where
  capitalCountryRelation foodCountryRelation : FineRelation

data CoarsePropertyCode : Set where
  countryOfXProperty : CoarsePropertyCode

data PreciseRelationKind : Set where
  capitalOfKind foodOriginKind : PreciseRelationKind

propertyCode : FineRelation → CoarsePropertyCode
propertyCode capitalCountryRelation = countryOfXProperty
propertyCode foodCountryRelation = countryOfXProperty

preciseRelation : FineRelation → PreciseRelationKind
preciseRelation capitalCountryRelation = capitalOfKind
preciseRelation foodCountryRelation = foodOriginKind

propertyCodeCollision :
  Compression.CompressionFailureWitness propertyCode preciseRelation
propertyCodeCollision =
  Compression.compressionFailureWitness
    capitalCountryRelation
    foodCountryRelation
    refl
    (λ ())

propertyCodeCannotRealizePreciseRelation :
  RepresentationRealizationWitness propertyCode preciseRelation → ⊥
propertyCodeCannotRealizePreciseRelation =
  representationCollisionBlocksRealization propertyCodeCollision

------------------------------------------------------------------------
-- Situated-meaning witness: equal compact relation code need not determine
-- social meaning when history/relation differs.
------------------------------------------------------------------------

data SituatedUtterance : Set where
  sameCodeRepairingContext sameCodeHostileContext : SituatedUtterance

data CompactRelationCode : Set where compactCode : CompactRelationCode

data SituatedMeaning : Set where
  reparativeMeaning hostileMeaning : SituatedMeaning

compactRelation : SituatedUtterance → CompactRelationCode
compactRelation _ = compactCode

situatedMeaning : SituatedUtterance → SituatedMeaning
situatedMeaning sameCodeRepairingContext = reparativeMeaning
situatedMeaning sameCodeHostileContext = hostileMeaning

situatedMeaningCollision :
  Compression.CompressionFailureWitness compactRelation situatedMeaning
situatedMeaningCollision =
  Compression.compressionFailureWitness
    sameCodeRepairingContext
    sameCodeHostileContext
    refl
    (λ ())

compactRelationCannotRealizeSituatedMeaning :
  RepresentationRealizationWitness compactRelation situatedMeaning → ⊥
compactRelationCannotRealizeSituatedMeaning =
  representationCollisionBlocksRealization situatedMeaningCollision

record RelationRepresentationRealizationBoundary : Set where
  constructor relationRepresentationRealizationBoundary
  field
    compactCodeImpliesCompleteRelation : Bool
    compactCodeImpliesCompleteRelationIsFalse :
      compactCodeImpliesCompleteRelation ≡ false

    successfulTaskCompressionImpliesTargetRealization : Bool
    successfulTaskCompressionImpliesTargetRealizationIsFalse :
      successfulTaskCompressionImpliesTargetRealization ≡ false

    futureSafeCompressionImpliesTargetRealization : Bool
    futureSafeCompressionImpliesTargetRealizationIsFalse :
      futureSafeCompressionImpliesTargetRealization ≡ false

    realizationRequiresExplicitCommutingWitness : Bool
    realizationRequiresExplicitCommutingWitnessIsTrue :
      realizationRequiresExplicitCommutingWitness ≡ true

    targetRealizationImpliesNormativeAuthority : Bool
    targetRealizationImpliesNormativeAuthorityIsFalse :
      targetRealizationImpliesNormativeAuthority ≡ false

canonicalRelationRepresentationRealizationBoundary :
  RelationRepresentationRealizationBoundary
canonicalRelationRepresentationRealizationBoundary =
  relationRepresentationRealizationBoundary
    false refl
    false refl
    false refl
    true refl
    false refl
