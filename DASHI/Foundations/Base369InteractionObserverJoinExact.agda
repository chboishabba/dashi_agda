module DASHI.Foundations.Base369InteractionObserverJoinExact where

------------------------------------------------------------------------
-- BASE369 TRANSVERSE OBSERVERS
--
-- The repo-native 27^3 = 3^9 interaction/appraisal carrier already has two
-- exact projections:
--
--   forgetBlockOrientation : State -> BlockOrientationQuotient
--   aggregateSum           : State -> Integer
--
-- Base369InteractionAntipodalFibreExact proves cross-collisions in both
-- directions.  This module upgrades those witnesses to exact non-factorisation
-- statements and gives the native universal property of the paired observer.
--
-- The generic observer-lattice version belongs to PR #584 in
-- DASHI.Core.ObserverIncomparabilityAndJoinExact.  This module deliberately
-- avoids copying that core into the #587 stack.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Integer using (ℤ)
open import Data.Product using (_×_; _,_; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality using (sym; trans; cong; cong₂)

import DASHI.Foundations.Base369InteractionAppraisalCubeExact as Cube
import DASHI.Foundations.Base369InteractionAntipodalFibreExact as Interaction

State : Set
State = Cube.OneRoundInteractionState

Block : Set
Block = Interaction.BlockOrientationQuotient

blockObserver : State → Block
blockObserver = Interaction.forgetBlockOrientation

sumObserver : State → ℤ
sumObserver = Interaction.aggregateSum

jointObserver : State → Block × ℤ
jointObserver state = blockObserver state , sumObserver state

------------------------------------------------------------------------
-- Exact no-decoder theorems in both directions.
------------------------------------------------------------------------

record BlockFactorsThroughSum : Set₁ where
  constructor blockFactorsThroughSum
  field
    decodeBlock : ℤ → Block
    blockFactorisation : (state : State) →
      blockObserver state ≡ decodeBlock (sumObserver state)

open BlockFactorsThroughSum public

blockCannotFactorThroughSum : BlockFactorsThroughSum → ⊥
blockCannotFactorThroughSum factor =
  proj₂ Interaction.aggregateCollisionSeparatedByBlockOrientation
    (trans
      (blockFactorisation factor Interaction.structuralZeroRound)
      (trans
        (cong (decodeBlock factor)
          (proj₁ Interaction.aggregateCollisionSeparatedByBlockOrientation))
        (sym (blockFactorisation factor Interaction.cancellationZeroRound))))

record SumFactorsThroughBlock : Set₁ where
  constructor sumFactorsThroughBlock
  field
    decodeSum : Block → ℤ
    sumFactorisation : (state : State) →
      sumObserver state ≡ decodeSum (blockObserver state)

open SumFactorsThroughBlock public

sumCannotFactorThroughBlock : SumFactorsThroughBlock → ⊥
sumCannotFactorThroughBlock factor =
  proj₂ Interaction.blockOrientationCollisionSeparatedByAggregate
    (trans
      (sumFactorisation factor Interaction.allPositiveRound)
      (trans
        (cong (decodeSum factor)
          (proj₁ Interaction.blockOrientationCollisionSeparatedByAggregate))
        (sym (sumFactorisation factor Interaction.baseFlipped))))

record TransverseProjectionIncomparability : Set₁ where
  constructor transverseProjectionIncomparability
  field
    blockDoesNotFactorThroughSum : BlockFactorsThroughSum → ⊥
    sumDoesNotFactorThroughBlock : SumFactorsThroughBlock → ⊥

canonicalTransverseProjectionIncomparability :
  TransverseProjectionIncomparability
canonicalTransverseProjectionIncomparability =
  transverseProjectionIncomparability
    blockCannotFactorThroughSum
    sumCannotFactorThroughBlock

------------------------------------------------------------------------
-- Native least-joint universal property in factorisation form.
--
-- If a common observer carries exact decoders for BOTH transverse coordinates,
-- then it carries an exact decoder for the pair.  Conversely the pair projects
-- to each coordinate by proj1/proj2.
------------------------------------------------------------------------

record CommonCarriesBoth (Common : Set) (common : State → Common) : Set₁ where
  constructor commonCarriesBoth
  field
    blockFromCommon : Common → Block
    sumFromCommon : Common → ℤ
    blockFactors : (state : State) →
      blockObserver state ≡ blockFromCommon (common state)
    sumFactors : (state : State) →
      sumObserver state ≡ sumFromCommon (common state)

open CommonCarriesBoth public

record JointFactorsThrough {Common : Set} (common : State → Common) : Set₁ where
  constructor jointFactorsThrough
  field
    jointFromCommon : Common → Block × ℤ
    jointFactorisation : (state : State) →
      jointObserver state ≡ jointFromCommon (common state)

open JointFactorsThrough public

commonCarryingBothFactorsJoint :
  ∀ {Common : Set} {common : State → Common} →
  CommonCarriesBoth Common common →
  JointFactorsThrough common
commonCarryingBothFactorsJoint carried =
  jointFactorsThrough
    (λ value → blockFromCommon carried value , sumFromCommon carried value)
    (λ state →
      cong₂ _,_
        (blockFactors carried state)
        (sumFactors carried state))

jointCarriesBlock :
  (state : State) → blockObserver state ≡ proj₁ (jointObserver state)
jointCarriesBlock state = refl

jointCarriesSum :
  (state : State) → sumObserver state ≡ proj₂ (jointObserver state)
jointCarriesSum state = refl

------------------------------------------------------------------------
-- Query-facing interpretation.
------------------------------------------------------------------------

record Base369ObserverJoinBoundary : Set where
  field
    aggregateObserverUniversallyFinerThanBlockObserver : Bool
    blockObserverUniversallyFinerThanAggregateObserver : Bool
    eitherIndividualObserverInvalid : Bool
    jointObserverRetainsBothCoordinates : Bool
    anyCommonObserverCarryingBothFactorsTheJoint : Bool
    jointObserverAutomaticallyWorldComplete : Bool

canonicalBase369ObserverJoinBoundary : Base369ObserverJoinBoundary
canonicalBase369ObserverJoinBoundary = record
  { aggregateObserverUniversallyFinerThanBlockObserver = false
  ; blockObserverUniversallyFinerThanAggregateObserver = false
  ; eitherIndividualObserverInvalid = false
  ; jointObserverRetainsBothCoordinates = true
  ; anyCommonObserverCarryingBothFactorsTheJoint = true
  ; jointObserverAutomaticallyWorldComplete = false
  }
