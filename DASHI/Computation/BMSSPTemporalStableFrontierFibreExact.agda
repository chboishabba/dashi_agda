module DASHI.Computation.BMSSPTemporalStableFrontierFibreExact where

-- Temporal same-object BMSSP frontier identity.
-- Pull exposure, residual tail, pivot/work certificates, and recursive motion
-- are fields over one literal time-indexed frontier state rather than separate
-- abstract carriers connected only by prose.

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Nat using (Nat; suc)

import DASHI.Computation.PathfindingTemporalFibreEvolutionExact as Temporal

------------------------------------------------------------------------
-- 1. Stable carrier identities over recursion/search time.
------------------------------------------------------------------------

record BMSSPFrontierState : Set where
  constructor bmsspFrontierState
  field
    exposedPrefixCode : Nat
    residualTailCode : Nat
    completedWorkCode : Nat
    pivotCode : Nat
    upperBoundCode : Nat

open BMSSPFrontierState public

record BMSSPVisibleFrontier : Set where
  constructor bmsspVisibleFrontier
  field
    prefixCode : Nat
    workCode : Nat
    pivotSummaryCode : Nat
    boundCode : Nat

open BMSSPVisibleFrontier public

record BMSSPResidualTail : Set where
  constructor bmsspResidualTail
  field
    tailCode : Nat

open BMSSPResidualTail public

------------------------------------------------------------------------
-- 2. One literal state supplies both visible and residual carriers.
------------------------------------------------------------------------

observeBMSSP : Nat → BMSSPFrontierState → BMSSPVisibleFrontier
observeBMSSP t s =
  bmsspVisibleFrontier
    (exposedPrefixCode s)
    (completedWorkCode s)
    (pivotCode s)
    (upperBoundCode s)

residualBMSSP : Nat → BMSSPFrontierState → BMSSPResidualTail
residualBMSSP t s = bmsspResidualTail (residualTailCode s)

------------------------------------------------------------------------
-- 3. Abstract recursive step over the same carrier.
--
-- Concrete BMSSP mechanics will refine this transition.  The important same-
-- object seam is already fixed: recursive motion consumes and returns the same
-- named frontier type, so Pull/work/pivot/tail projections cannot silently
-- drift onto unrelated carriers.
------------------------------------------------------------------------

record BMSSPRecursiveStep : Set₁ where
  constructor bmsspRecursiveStep
  field
    advance : Nat → BMSSPFrontierState → BMSSPFrontierState

    advanceVisible : Nat → BMSSPVisibleFrontier → BMSSPVisibleFrontier
    advanceResidual : Nat → BMSSPResidualTail → BMSSPResidualTail

    visibleCommutes :
      (t : Nat) (s : BMSSPFrontierState) →
      observeBMSSP (suc t) (advance t s) ≡
      advanceVisible t (observeBMSSP t s)

open BMSSPRecursiveStep public

asTemporalFibre : BMSSPRecursiveStep → Temporal.TemporalPathfindingFibre
asTemporalFibre R =
  Temporal.temporalPathfindingFibre
    Nat
    (λ t → BMSSPFrontierState)
    (λ t → BMSSPVisibleFrontier)
    (λ t → BMSSPResidualTail)
    observeBMSSP
    residualBMSSP
    suc
    (advance R)
    (advanceVisible R)
    (advanceResidual R)
    (visibleCommutes R)

------------------------------------------------------------------------
-- 4. Named same-object projections.
------------------------------------------------------------------------

pullPrefix : BMSSPFrontierState → Nat
pullPrefix = exposedPrefixCode

workCarrier : BMSSPFrontierState → Nat
workCarrier = completedWorkCode

pivotCarrier : BMSSPFrontierState → Nat
pivotCarrier = pivotCode

residualTailCarrier : BMSSPFrontierState → Nat
residualTailCarrier = residualTailCode

record BMSSPSameObjectBoundary : Set where
  constructor bmsspSameObjectBoundary
  field
    pullAndPivotsProjectSameLiteralFrontier : Bool
    pullAndPivotsProjectSameLiteralFrontierIsTrue :
      pullAndPivotsProjectSameLiteralFrontier ≡ true

    recursiveStepReturnsSameNamedFrontierType : Bool
    recursiveStepReturnsSameNamedFrontierTypeIsTrue :
      recursiveStepReturnsSameNamedFrontierType ≡ true

    tailAtNextTimeNeedEqualTailAtCurrentTime : Bool
    tailAtNextTimeNeedEqualTailAtCurrentTimeIsFalse :
      tailAtNextTimeNeedEqualTailAtCurrentTime ≡ false

    natProjectionIsTheFrontierIdentity : Bool
    natProjectionIsTheFrontierIdentityIsFalse :
      natProjectionIsTheFrontierIdentity ≡ false

canonicalBMSSPSameObjectBoundary : BMSSPSameObjectBoundary
canonicalBMSSPSameObjectBoundary =
  bmsspSameObjectBoundary true refl true refl false refl false refl
