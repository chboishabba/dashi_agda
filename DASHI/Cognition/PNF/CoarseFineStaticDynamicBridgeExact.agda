module DASHI.Cognition.PNF.CoarseFineStaticDynamicBridgeExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Product using (proj₂; _,_)

import DASHI.Core.CoarseFineFabricCalculusExact as Calculus
import DASHI.Core.DynamicalQuotientSafety as Dynamic
import DASHI.Cognition.PNF.TerminalisationDefectRegression as Existing

------------------------------------------------------------------------
-- STATIC + DYNAMIC WITNESS ON THE SAME RESIDUAL FIBRE
--
-- Existing.residualProjection forgets the second Bool while the existing
-- ProvenanceBearingQuotient retains it as an exact reopening receipt.
-- The pair (false,true) / (false,false):
--   * collides under the current projection,
--   * is separated by the retained residual query proj₂,
--   * and the same existing exposeResidual action later separates the coarse
--     observations, yielding TerminalisationDefect.
--
-- This example inhabits both notions.  It does NOT prove that either notion
-- implies the other for arbitrary projections/dynamics.
------------------------------------------------------------------------

residualStaticCollision :
  Calculus.ProjectionCollision Existing.residualProjection proj₂
residualStaticCollision =
  Calculus.projectionCollision
    (false , true)
    (false , false)
    refl
    Existing.trueNotFalse

residualStaticNonFactorability :
  (coarseObserve : Bool → Bool) →
  ((state : Existing.ResidualState) →
    proj₂ state ≡ coarseObserve (Existing.residualProjection state)) →
  ⊥
residualStaticNonFactorability =
  Calculus.consumerCannotFactorThroughProjection residualStaticCollision

residualDynamicDefect :
  Dynamic.TerminalisationDefect
    Existing.residualSystem
    Existing.residualProjection
residualDynamicDefect =
  Existing.residualProjectionTerminalisationDefect

residualDynamicSafetyRefuted :
  Dynamic.DynamicConsumerSafety
    Existing.residualSystem
    Existing.residualProjection →
  ⊥
residualDynamicSafetyRefuted safety =
  Dynamic.terminalisationDefectContradictsSafety
    safety
    residualDynamicDefect

record StaticDynamicBridgeBoundary : Set where
  constructor staticDynamicBridgeBoundary
  field
    sameConcretePairHasStaticCollision : Bool
    sameProjectionHasDynamicDefect : Bool
    exactResidualReopeningExistsInParent : Bool
    staticCollisionAutomaticallyCreatesDynamicDefect : Bool
    dynamicDefectAutomaticallyCreatesStaticCollision : Bool
    staticConsumerNonFactorabilityEqualsTraceUnsafety : Bool

canonicalStaticDynamicBridgeBoundary : StaticDynamicBridgeBoundary
canonicalStaticDynamicBridgeBoundary =
  staticDynamicBridgeBoundary
    true
    true
    true
    false
    false
    false
