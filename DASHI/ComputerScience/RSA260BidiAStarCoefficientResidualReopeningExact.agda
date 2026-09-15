module DASHI.ComputerScience.RSA260BidiAStarCoefficientResidualReopeningExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Data.Empty using (⊥)

import DASHI.Core.CoarseFineRelativeFibreExact as Fibre
import DASHI.ComputerScience.RSA260BidiAStarRelationAugmentedEncodingCollisionExact as Collision

------------------------------------------------------------------------
-- RSA-260 BIDI A* COEFFICIENT-RESIDUAL REOPENING
--
-- The relation-augmented scalar/rank encoding still collides for generator
-- identity.  Rather than accumulating more scalar coordinates, retain the
-- generator coefficient identity as the relative-fine residual over the coarse
-- packet.  This is exactly the repo-native coarse/fine reopening pattern.
--
-- The present finite geometry uses the rotate3/affine7 collision witness.  It
-- does NOT claim that a digest is an algebraically canonical generator, or that
-- the full coefficient blob is the globally minimal residual.
------------------------------------------------------------------------

collisionBoundary : Collision.RelationAugmentedEncodingBoundary
collisionBoundary = Collision.canonicalRelationAugmentedEncodingBoundary

data GeneratorFineState : Set where
  rotate3FineState : GeneratorFineState
  affine7FineState : GeneratorFineState

data RelationAugmentedCoarse : Set where
  degree17ZeroExtensionRank128Rel16Shift120 : RelationAugmentedCoarse

data GeneratorCoefficientResidual : Set where
  rotate3CoefficientResidual : GeneratorCoefficientResidual
  affine7CoefficientResidual : GeneratorCoefficientResidual

coarseEncoding : GeneratorFineState → RelationAugmentedCoarse
coarseEncoding _ = degree17ZeroExtensionRank128Rel16Shift120

coefficientResidual : GeneratorFineState → GeneratorCoefficientResidual
coefficientResidual rotate3FineState = rotate3CoefficientResidual
coefficientResidual affine7FineState = affine7CoefficientResidual

reopenGenerator :
  RelationAugmentedCoarse → GeneratorCoefficientResidual → GeneratorFineState
reopenGenerator degree17ZeroExtensionRank128Rel16Shift120 rotate3CoefficientResidual =
  rotate3FineState
reopenGenerator degree17ZeroExtensionRank128Rel16Shift120 affine7CoefficientResidual =
  affine7FineState

reopenGeneratorExact :
  (state : GeneratorFineState) →
  reopenGenerator (coarseEncoding state) (coefficientResidual state) ≡ state
reopenGeneratorExact rotate3FineState = refl
reopenGeneratorExact affine7FineState = refl

GeneratorCoefficientReopening : Set₁
GeneratorCoefficientReopening = Fibre.CoarseFineReopening GeneratorFineState

generatorCoefficientReopening : GeneratorCoefficientReopening
generatorCoefficientReopening =
  Fibre.coarseFineReopening
    RelationAugmentedCoarse
    GeneratorCoefficientResidual
    coarseEncoding
    coefficientResidual
    reopenGenerator
    reopenGeneratorExact

data GeneratorIdentityObservation : Set where
  rotate3GeneratorIdentity : GeneratorIdentityObservation
  affine7GeneratorIdentity : GeneratorIdentityObservation

generatorIdentityObserve : GeneratorFineState → GeneratorIdentityObservation
generatorIdentityObserve rotate3FineState = rotate3GeneratorIdentity
generatorIdentityObserve affine7FineState = affine7GeneratorIdentity

GeneratorFineSensitiveConsumer : Set
GeneratorFineSensitiveConsumer =
  Fibre.FineSensitiveConsumer generatorCoefficientReopening generatorIdentityObserve

generatorFineSensitiveConsumer : GeneratorFineSensitiveConsumer
generatorFineSensitiveConsumer =
  Fibre.fineSensitiveConsumer
    rotate3FineState
    affine7FineState
    refl
    (λ ())
    "fixed BASEX/BASEY; rotate3 and affine7 share the relation-augmented coarse packet but have distinct recovered generator coefficient digests"

coarsePlusCoefficientResidualDeterminesGeneratorState :
  {left right : GeneratorFineState} →
  coarseEncoding left ≡ coarseEncoding right →
  coefficientResidual left ≡ coefficientResidual right →
  left ≡ right
coarsePlusCoefficientResidualDeterminesGeneratorState =
  Fibre.coarseAndRelativeFineDetermineState generatorCoefficientReopening

------------------------------------------------------------------------
-- Interpretation boundary.
------------------------------------------------------------------------

record CoefficientResidualReopeningBoundary : Set where
  constructor coefficient-residual-reopening-boundary
  field
    relationAugmentedCollisionInherited : Bool
    scalarRankPacketRetainedAsCoarseCoordinate : Bool
    generatorCoefficientIdentityRetainedAsRelativeFineResidual : Bool
    exactFiniteReopeningPaid : Bool
    coarseOnlyFailsGeneratorIdentityConsumer : Bool
    coarsePlusResidualDeterminesFiniteGeneratorState : Bool
    coefficientDigestIsCanonicalAlgebraicGeneratorIdentity : Bool
    fullCoefficientResidualProvedGloballyMinimal : Bool
    productionAStarBytesAcquired : Bool
open CoefficientResidualReopeningBoundary public

canonicalCoefficientResidualReopeningBoundary : CoefficientResidualReopeningBoundary
canonicalCoefficientResidualReopeningBoundary =
  coefficient-residual-reopening-boundary
    true
    true
    true
    true
    true
    true
    false
    false
    false

data CoefficientResidualReopeningResidual : Set where
  compressGeneratorCoefficientResidualConsumerSafely : CoefficientResidualReopeningResidual
  testCoefficientSketchCollision : CoefficientResidualReopeningResidual
  compileProductionShapedAStarDecoder : CoefficientResidualReopeningResidual
  acquireSameObjectProjectedAStarBytes : CoefficientResidualReopeningResidual
  fallbackToSameObjectFSolsIfAStarUnavailable : CoefficientResidualReopeningResidual

firstCoefficientResidualReopeningResidual : CoefficientResidualReopeningResidual
firstCoefficientResidualReopeningResidual =
  compressGeneratorCoefficientResidualConsumerSafely

------------------------------------------------------------------------
-- WrongType firewalls.
------------------------------------------------------------------------

data ExactFiniteReopeningMeansGlobalMinimalResidual : Set where
data ByteDigestMeansCanonicalAlgebraicIdentity : Set where
data SyntheticResidualMeansProductionCustody : Set where

finiteReopeningDoesNotCreateGlobalMinimality :
  ExactFiniteReopeningMeansGlobalMinimalResidual → ⊥
finiteReopeningDoesNotCreateGlobalMinimality ()

digestDoesNotCreateCanonicalAlgebraicIdentity :
  ByteDigestMeansCanonicalAlgebraicIdentity → ⊥
digestDoesNotCreateCanonicalAlgebraicIdentity ()

syntheticResidualDoesNotCreateProductionCustody :
  SyntheticResidualMeansProductionCustody → ⊥
syntheticResidualDoesNotCreateProductionCustody ()
