module DASHI.Physics.Closure.NSCompactGammaNormalizedAdaptiveFirstExit where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ; _,_)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_; inj₁; inj₂)

------------------------------------------------------------------------
-- Corrected first-exit surface after the absolute packet-floor falsification.
--
-- The packet face is scale invariant: E_packet / E_total.  A hysteretic chart
-- switch is an allowed continuation event, not an uncontrolled exit.
------------------------------------------------------------------------

data NormalizedAnalyticFace : Set where
  gammaFloorFace : NormalizedAnalyticFace
  packetFractionFloorFace : NormalizedAnalyticFace
  offPacketCeilingFace : NormalizedAnalyticFace
  sizeCeilingFace : NormalizedAnalyticFace

record NormalizedBoundaryOrder (i : Level) : Set (lsuc i) where
  field
    Scalar : Set i
    StrictlyPositive NonPositive : Scalar → Set i
    positiveAndNonpositiveContradict : ∀ value →
      StrictlyPositive value → NonPositive value → ⊥

open NormalizedBoundaryOrder public

record NormalizedAdaptiveFirstExitReduction
    {i : Level}
    (O : NormalizedBoundaryOrder i) : Set (lsuc i) where
  field
    Time State : Set i

    FirstExit : Time → State → Set i
    BoundaryHit : NormalizedAnalyticFace → Time → State → Set i
    ChartSwitch : Time → State → Set i

    firstExitProducesBoundaryOrSwitch : ∀ τ u →
      FirstExit τ u →
      (Σ NormalizedAnalyticFace (λ face → BoundaryHit face τ u))
      ⊎ ChartSwitch τ u

    lowerDiniDerivative :
      NormalizedAnalyticFace → Time → State → Scalar O

    ContinuousAtBoundary :
      NormalizedAnalyticFace → Time → State → Set i
    LowerDiniDerivativeExists :
      NormalizedAnalyticFace → Time → State → Set i

    boundaryContinuity : ∀ face τ u →
      BoundaryHit face τ u → ContinuousAtBoundary face τ u

    boundaryDiniRegularity : ∀ face τ u →
      BoundaryHit face τ u → LowerDiniDerivativeExists face τ u

    strictInwardDiniEstimate : ∀ face τ u →
      BoundaryHit face τ u →
      StrictlyPositive O (lowerDiniDerivative face τ u)

    firstExitDiniSign : ∀ face τ u →
      FirstExit τ u → BoundaryHit face τ u →
      NonPositive O (lowerDiniDerivative face τ u)

    -- The hysteretic update selects the new chart and stays in the admissible
    -- union, so the event cannot be the terminal first exit of that union.
    controlledChartSwitchIsNotExit : ∀ τ u →
      FirstExit τ u → ChartSwitch τ u → ⊥

open NormalizedAdaptiveFirstExitReduction public

normalizedAdaptiveFirstExitImpossible :
  ∀ {i} {O : NormalizedBoundaryOrder i} →
  (R : NormalizedAdaptiveFirstExitReduction O) →
  ∀ τ u → FirstExit R τ u → ⊥
normalizedAdaptiveFirstExitImpossible {O = O} R τ u exit
  with firstExitProducesBoundaryOrSwitch R τ u exit
... | inj₁ (face , hit) =
  positiveAndNonpositiveContradict O
    (lowerDiniDerivative R face τ u)
    (strictInwardDiniEstimate R face τ u hit)
    (firstExitDiniSign R face τ u exit hit)
... | inj₂ switch = controlledChartSwitchIsNotExit R τ u exit switch
