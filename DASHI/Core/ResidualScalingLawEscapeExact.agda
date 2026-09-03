module DASHI.Core.ResidualScalingLawEscapeExact where

open import DASHI.Core.Prelude

import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- RESIDUAL SCALING-LAW ESCAPE
--
-- Generic theorem shape for situations where a coarse consumer chart makes a
-- target appear to obey a one-coordinate scaling law, while a finer residual
-- coordinate can separate states collapsed by that chart.
--
-- This module proves only observer mathematics.  It does not claim that any
-- particular physical system actually supplies the required separating pair.
------------------------------------------------------------------------

record ResidualScalingWitness
    {State Coarse Residual Target : Set}
    (coarse : Observer.Observer State Coarse)
    (residual : Observer.Observer State Residual)
    (target : Observer.Observer State Target) : Set where
  constructor residual-scaling-witness
  field
    left right : State
    sameCoarse : coarse left ≡ coarse right
    residualSeparates : residual left ≡ residual right → ⊥
    targetSeparates : target left ≡ target right → ⊥

open ResidualScalingWitness public

ScalingLawDescends :
  ∀ {State Coarse Target : Set} →
  Observer.Observer State Coarse →
  Observer.Observer State Target →
  Set
ScalingLawDescends {State} {Coarse} {Target} coarse target =
  Σ (Coarse → Target)
    (λ reconstruct →
      ∀ state → reconstruct (coarse state) ≡ target state)

residualScalingWitnessBlocksCoarseScalingLaw :
  ∀ {State Coarse Residual Target : Set}
    {coarse : Observer.Observer State Coarse}
    {residual : Observer.Observer State Residual}
    {target : Observer.Observer State Target} →
  ResidualScalingWitness coarse residual target →
  ScalingLawDescends coarse target →
  ⊥
residualScalingWitnessBlocksCoarseScalingLaw witness descent =
  targetSeparates witness
    (trans
      (sym (commutes (left witness)))
      (trans
        (cong reconstruct (sameCoarse witness))
        (commutes (right witness))))
  where
    reconstruct = proj₁ descent
    commutes = proj₂ descent

refinedScalingObservation :
  ∀ {State Coarse Residual : Set} →
  Observer.Observer State Coarse →
  Observer.Observer State Residual →
  Observer.Observer State (Coarse × Residual)
refinedScalingObservation = Observer.pairObserver

refinedScalingObservationRefinesCoarse :
  ∀ {State Coarse Residual : Set}
    (coarse : Observer.Observer State Coarse)
    (residual : Observer.Observer State Residual) →
  Observer.Refines coarse (refinedScalingObservation coarse residual)
refinedScalingObservationRefinesCoarse = Observer.pairRefinesLeft

residualScalingWitnessGivesStrictRefinement :
  ∀ {State Coarse Residual Target : Set}
    {coarse : Observer.Observer State Coarse}
    {residual : Observer.Observer State Residual}
    {target : Observer.Observer State Target} →
  ResidualScalingWitness coarse residual target →
  Observer.StrictRefinement coarse (refinedScalingObservation coarse residual)
residualScalingWitnessGivesStrictRefinement witness =
  Observer.strictPairRefinement
    _ _
    (left witness)
    (right witness)
    (sameCoarse witness)
    (residualSeparates witness)

------------------------------------------------------------------------
-- Boundary: adding a residual coordinate creates a strictly finer observer
-- when a witness exists; it does not by itself prove improved physical
-- performance, causality, kinetics, selectivity, or experimental validity.
------------------------------------------------------------------------

record ResidualScalingBoundary : Set where
  constructor residual-scaling-boundary
  field
    coarseChartCanHideTargetRelevantResidual : Bool
    coarseChartCanHideTargetRelevantResidualIsTrue :
      coarseChartCanHideTargetRelevantResidual ≡ true

    separatingResidualBlocksCoarseDescent : Bool
    separatingResidualBlocksCoarseDescentIsTrue :
      separatingResidualBlocksCoarseDescent ≡ true

    residualReopeningAutomaticallyProvesBetterPerformance : Bool
    residualReopeningAutomaticallyProvesBetterPerformanceIsFalse :
      residualReopeningAutomaticallyProvesBetterPerformance ≡ false

canonicalResidualScalingBoundary : ResidualScalingBoundary
canonicalResidualScalingBoundary =
  residual-scaling-boundary true refl true refl false refl
