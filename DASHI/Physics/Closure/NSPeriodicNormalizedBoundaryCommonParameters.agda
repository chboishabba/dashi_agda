module DASHI.Physics.Closure.NSPeriodicNormalizedBoundaryCommonParameters where

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Sigma using (Σ)
open import Data.Empty using (⊥)
open import Data.Sum.Base using (_⊎_)

import DASHI.Physics.Closure.NSCompactGammaNormalizedAdaptiveFirstExit as Exit
import DASHI.Physics.Closure.NSCompactGammaNormalizedBoundaryInwardnessCompletion as Boundary
open import DASHI.Physics.YangMills.CompactLieProofLevel

------------------------------------------------------------------------
-- Common-parameter constructor for the four normalized boundary faces.
--
-- Four independently true estimates are insufficient if they use incompatible
-- values of R, gamma*, rho*, eta*, M or the potential weights.  This module
-- requires one selected parameter object and one admissibility witness to feed
-- all four strict Dini estimates, then constructs the existing first-exit input
-- package.
------------------------------------------------------------------------

record CommonParameterizedNormalizedBoundaryInputs
    {i : Level}
    (O : Exit.NormalizedBoundaryOrder i) : Set (lsuc i) where
  field
    Time State Parameters : Set i

    selectedParameters : Parameters
    ParameterAdmissible : Parameters → Set i
    selectedParametersAdmissible :
      ParameterAdmissible selectedParameters

    FirstExit : Time → State → Set i
    BoundaryHit : Exit.NormalizedAnalyticFace → Time → State → Set i
    ChartSwitch : Time → State → Set i

    firstExitProducesBoundaryOrSwitch : ∀ τ u →
      FirstExit τ u →
      (Σ Exit.NormalizedAnalyticFace (λ face → BoundaryHit face τ u))
      ⊎ ChartSwitch τ u

    lowerDiniDerivative :
      Parameters →
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
      ParameterAdmissible selectedParameters →
      BoundaryHit Exit.gammaFloorFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative selectedParameters Exit.gammaFloorFace τ u)

    packetFractionFloorStrictlyInward : ∀ τ u →
      ParameterAdmissible selectedParameters →
      BoundaryHit Exit.packetFractionFloorFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative selectedParameters Exit.packetFractionFloorFace τ u)

    offPacketCeilingStrictlyInward : ∀ τ u →
      ParameterAdmissible selectedParameters →
      BoundaryHit Exit.offPacketCeilingFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative selectedParameters Exit.offPacketCeilingFace τ u)

    sizeCeilingStrictlyInward : ∀ τ u →
      ParameterAdmissible selectedParameters →
      BoundaryHit Exit.sizeCeilingFace τ u →
      Exit.StrictlyPositive O
        (lowerDiniDerivative selectedParameters Exit.sizeCeilingFace τ u)

    firstExitDiniSign : ∀ face τ u →
      FirstExit τ u → BoundaryHit face τ u →
      Exit.NonPositive O
        (lowerDiniDerivative selectedParameters face τ u)

    controlledChartSwitchIsNotExit : ∀ τ u →
      FirstExit τ u → ChartSwitch τ u → ⊥

open CommonParameterizedNormalizedBoundaryInputs public

commonParametersToNormalizedBoundaryInputs :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  CommonParameterizedNormalizedBoundaryInputs O →
  Boundary.NormalizedBoundaryPDEInputs O
commonParametersToNormalizedBoundaryInputs P = record
  { Time = Time P
  ; State = State P
  ; FirstExit = FirstExit P
  ; BoundaryHit = BoundaryHit P
  ; ChartSwitch = ChartSwitch P
  ; firstExitProducesBoundaryOrSwitch = firstExitProducesBoundaryOrSwitch P
  ; lowerDiniDerivative =
      lowerDiniDerivative P (selectedParameters P)
  ; ContinuousAtBoundary = ContinuousAtBoundary P
  ; LowerDiniDerivativeExists = LowerDiniDerivativeExists P
  ; boundaryContinuity = boundaryContinuity P
  ; boundaryDiniRegularity = boundaryDiniRegularity P
  ; gammaFloorStrictlyInward = λ τ u hit →
      gammaFloorStrictlyInward P τ u
        (selectedParametersAdmissible P) hit
  ; packetFractionFloorStrictlyInward = λ τ u hit →
      packetFractionFloorStrictlyInward P τ u
        (selectedParametersAdmissible P) hit
  ; offPacketCeilingStrictlyInward = λ τ u hit →
      offPacketCeilingStrictlyInward P τ u
        (selectedParametersAdmissible P) hit
  ; sizeCeilingStrictlyInward = λ τ u hit →
      sizeCeilingStrictlyInward P τ u
        (selectedParametersAdmissible P) hit
  ; firstExitDiniSign = firstExitDiniSign P
  ; controlledChartSwitchIsNotExit = controlledChartSwitchIsNotExit P
  }

commonParameterizedBoundaryHasNoFirstExit :
  ∀ {i} {O : Exit.NormalizedBoundaryOrder i} →
  (P : CommonParameterizedNormalizedBoundaryInputs O) →
  ∀ τ u → FirstExit P τ u → ⊥
commonParameterizedBoundaryHasNoFirstExit P =
  Boundary.normalizedAdaptiveCoverageNoFirstExit
    (commonParametersToNormalizedBoundaryInputs P)

------------------------------------------------------------------------
-- Status: common-tuple coherence is checked.  The PDE frontier is now one
-- simultaneous feasibility problem for selectedParameters, rather than four
-- unrelated face estimates that could use mutually incompatible constants.
------------------------------------------------------------------------

normalizedBoundaryCommonParameterAssemblyLevel : ProofLevel
normalizedBoundaryCommonParameterAssemblyLevel = machineChecked
