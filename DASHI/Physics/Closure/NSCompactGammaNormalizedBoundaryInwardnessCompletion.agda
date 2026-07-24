module DASHI.Physics.Closure.NSCompactGammaNormalizedBoundaryInwardnessCompletion where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

import DASHI.Physics.Closure.NSCompactGammaNormalizedAdaptiveFirstExit as Exit
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Four-face PDE input surface for the corrected normalized/adaptive region.
--
-- The packet face is the scale-invariant packet fraction, not the falsified
-- absolute packet-energy floor.  The constructor below turns four separate
-- strict estimates into the generic no-first-exit theorem already proved in the
-- repository.
------------------------------------------------------------------------

record NormalizedBoundaryPDEInputs
    {i : Level}
    (O : Exit.NormalizedBoundaryOrder i) : Set (lsuc i) where
  field
    Time State : Set i

    FirstExit : Time → State → Set i
    BoundaryHit : Exit.NormalizedAnalyticFace → Time → State → Set i
    ChartSwitch : Time → State → Set i

    firstExitProducesBoundaryOrSwitch : ∀ τ u →
      FirstExit τ u →
      (Σ Exit.NormalizedAnalyticFace (λ face → BoundaryHit face τ u))
      ⊎ ChartSwitch τ u

    lowerDiniDerivative :
      Exit.NormalizedAnalyticFace → Time → State → Exit.Scalar O

    ContinuousAtBoundary :
      Exit.NormalizedAnalyticFace → Time → State → Set i
    LowerDiniDerivativeExists :
      Exit.NormalizedAnalyticFace → Time → State → Set i

    boundaryContinuity : ∀ face τ u →
      BoundaryHit face τ u → ContinuousAtBoundary face τ u

    boundaryDiniRegularity : ∀ face τ u →
      BoundaryHit face τ u → LowerDiniDerivativeExists face τ u

    gammaFloorStrictlyInward : ∀ τ u →
      BoundaryHit Exit.gammaFloorFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative Exit.gammaFloorFace τ u)

    packetFractionFloorStrictlyInward : ∀ τ u →
      BoundaryHit Exit.packetFractionFloorFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative Exit.packetFractionFloorFace τ u)

    offPacketCeilingStrictlyInward : ∀ τ u →
      BoundaryHit Exit.offPacketCeilingFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative Exit.offPacketCeilingFace τ u)

    sizeCeilingStrictlyInward : ∀ τ u →
      BoundaryHit Exit.sizeCeilingFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative Exit.sizeCeilingFace τ u)

    firstExitDiniSign : ∀ face τ u →
      FirstExit τ u → BoundaryHit face τ u →
      Exit.NonPositive O (lowerDiniDerivative face τ u)

    controlledChartSwitchIsNotExit : ∀ τ u →
      FirstExit τ u → ChartSwitch τ u → ⊥

open NormalizedBoundaryPDEInputs public

normalizedStrictInwardByFace :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  (P : NormalizedBoundaryPDEInputs O) →
  ∀ face τ u →
  BoundaryHit P face τ u →
  Exit.StrictlyPositive O (lowerDiniDerivative P face τ u)
normalizedStrictInwardByFace P Exit.gammaFloorFace τ u hit =
  gammaFloorStrictlyInward P τ u hit
normalizedStrictInwardByFace P Exit.packetFractionFloorFace τ u hit =
  packetFractionFloorStrictlyInward P τ u hit
normalizedStrictInwardByFace P Exit.offPacketCeilingFace τ u hit =
  offPacketCeilingStrictlyInward P τ u hit
normalizedStrictInwardByFace P Exit.sizeCeilingFace τ u hit =
  sizeCeilingStrictlyInward P τ u hit

normalizedBoundaryInputsToFirstExitReduction :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  NormalizedBoundaryPDEInputs O →
  Exit.NormalizedAdaptiveFirstExitReduction O
normalizedBoundaryInputsToFirstExitReduction P = record
  { Time = Time P
  ; State = State P
  ; FirstExit = FirstExit P
  ; BoundaryHit = BoundaryHit P
  ; ChartSwitch = ChartSwitch P
  ; firstExitProducesBoundaryOrSwitch = firstExitProducesBoundaryOrSwitch P
  ; lowerDiniDerivative = lowerDiniDerivative P
  ; ContinuousAtBoundary = ContinuousAtBoundary P
  ; LowerDiniDerivativeExists = LowerDiniDerivativeExists P
  ; boundaryContinuity = boundaryContinuity P
  ; boundaryDiniRegularity = boundaryDiniRegularity P
  ; strictInwardDiniEstimate = normalizedStrictInwardByFace P
  ; firstExitDiniSign = firstExitDiniSign P
  ; controlledChartSwitchIsNotExit = controlledChartSwitchIsNotExit P
  }

normalizedAdaptiveCoverageNoFirstExit :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  (P : NormalizedBoundaryPDEInputs O) →
  ∀ τ u → FirstExit P τ u → ⊥
normalizedAdaptiveCoverageNoFirstExit P =
  Exit.normalizedAdaptiveFirstExitImpossible
    (normalizedBoundaryInputsToFirstExitReduction P)

------------------------------------------------------------------------
-- Proof-level and fail-closed status.
------------------------------------------------------------------------

normalizedBoundaryFourFaceAssemblyLevel : ProofLevel
normalizedBoundaryFourFaceAssemblyLevel = machineChecked

normalizedGammaFloorInwardnessLevel : ProofLevel
normalizedGammaFloorInwardnessLevel = conditional

normalizedPacketFractionInwardnessLevel : ProofLevel
normalizedPacketFractionInwardnessLevel = conjectural

normalizedOffPacketInwardnessLevel : ProofLevel
normalizedOffPacketInwardnessLevel = conditional

normalizedSizeInwardnessLevel : ProofLevel
normalizedSizeInwardnessLevel = conditional

normalizedBoundaryPDEInputsInhabited : Bool
normalizedBoundaryPDEInputsInhabited = false
