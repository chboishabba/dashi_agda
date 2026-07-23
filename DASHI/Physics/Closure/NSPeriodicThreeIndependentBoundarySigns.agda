module DASHI.Physics.Closure.NSPeriodicThreeIndependentBoundarySigns where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)
open import Relation.Binary.PropositionalEquality using (subst; sym)

import DASHI.Physics.Closure.NSCompactGammaNormalizedAdaptiveFirstExit as Exit
import DASHI.Physics.Closure.NSCompactGammaNormalizedBoundaryInwardnessCompletion as Boundary
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Reduction from four named boundary faces to three independent PDE signs.
--
-- For complementary packet/off thresholds, the packet-fraction floor and the
-- off-packet ceiling are the same geometric face.  When the off-packet inward
-- defining function is eta* - off = packet - rho*, their inward Dini
-- derivatives are equal.  Hence Gamma, packet/off, and size are the only three
-- independent strict sign estimates.
------------------------------------------------------------------------

record ThreeIndependentNormalizedBoundaryInputs
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

    sizeCeilingStrictlyInward : ∀ τ u →
      BoundaryHit Exit.sizeCeilingFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative Exit.sizeCeilingFace τ u)

    offBoundaryIsPacketBoundary : ∀ τ u →
      BoundaryHit Exit.offPacketCeilingFace τ u →
      BoundaryHit Exit.packetFractionFloorFace τ u

    offInwardDerivativeEqualsPacket : ∀ τ u →
      BoundaryHit Exit.offPacketCeilingFace τ u →
      lowerDiniDerivative Exit.offPacketCeilingFace τ u
      ≡ lowerDiniDerivative Exit.packetFractionFloorFace τ u

    firstExitDiniSign : ∀ face τ u →
      FirstExit τ u → BoundaryHit face τ u →
      Exit.NonPositive O (lowerDiniDerivative face τ u)

    controlledChartSwitchIsNotExit : ∀ τ u →
      FirstExit τ u → ChartSwitch τ u → ⊥

open ThreeIndependentNormalizedBoundaryInputs public

threeFaceOffPacketStrictlyInward :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  (T : ThreeIndependentNormalizedBoundaryInputs O) →
  ∀ τ u →
  BoundaryHit T Exit.offPacketCeilingFace τ u →
  Exit.StrictlyPositive O
    (lowerDiniDerivative T Exit.offPacketCeilingFace τ u)
threeFaceOffPacketStrictlyInward T τ u offHit =
  subst
    (Exit.StrictlyPositive _)
    (sym (offInwardDerivativeEqualsPacket T τ u offHit))
    (packetFractionFloorStrictlyInward T τ u
      (offBoundaryIsPacketBoundary T τ u offHit))

threeIndependentSignsToBoundaryInputs :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  ThreeIndependentNormalizedBoundaryInputs O →
  Boundary.NormalizedBoundaryPDEInputs O
threeIndependentSignsToBoundaryInputs T = record
  { Time = Time T
  ; State = State T
  ; FirstExit = FirstExit T
  ; BoundaryHit = BoundaryHit T
  ; ChartSwitch = ChartSwitch T
  ; firstExitProducesBoundaryOrSwitch = firstExitProducesBoundaryOrSwitch T
  ; lowerDiniDerivative = lowerDiniDerivative T
  ; ContinuousAtBoundary = ContinuousAtBoundary T
  ; LowerDiniDerivativeExists = LowerDiniDerivativeExists T
  ; boundaryContinuity = boundaryContinuity T
  ; boundaryDiniRegularity = boundaryDiniRegularity T
  ; gammaFloorStrictlyInward = gammaFloorStrictlyInward T
  ; packetFractionFloorStrictlyInward = packetFractionFloorStrictlyInward T
  ; offPacketCeilingStrictlyInward = threeFaceOffPacketStrictlyInward T
  ; sizeCeilingStrictlyInward = sizeCeilingStrictlyInward T
  ; firstExitDiniSign = firstExitDiniSign T
  ; controlledChartSwitchIsNotExit = controlledChartSwitchIsNotExit T
  }

threeIndependentBoundarySignsGiveNoFirstExit :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  (T : ThreeIndependentNormalizedBoundaryInputs O) →
  ∀ τ u → FirstExit T τ u → ⊥
threeIndependentBoundarySignsGiveNoFirstExit T =
  Boundary.normalizedAdaptiveCoverageNoFirstExit
    (threeIndependentSignsToBoundaryInputs T)

------------------------------------------------------------------------
-- Status: the normalized boundary program has three independent PDE signs.
-- The packet/off coincidence and derivative equality are supplied by the exact
-- complement and quotient-duality theorems for the selected carrier.
------------------------------------------------------------------------

threeIndependentBoundarySignLevel : ProofLevel
threeIndependentBoundarySignLevel = machineChecked
