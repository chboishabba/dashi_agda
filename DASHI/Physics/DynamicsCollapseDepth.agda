module DASHI.Physics.DynamicsCollapseDepth where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DynamicsFixedPointUniqueness as DFPU
open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Bounded collapse-depth surface over a finite attractor package.
--
-- This module does not claim a canonical time observable, metric distance,
-- or continuum decay law. It only packages:
--   * one finite-carrier attractor surface,
--   * one depth-to-held function,
--   * and one exact witness that iterating by that depth lands at held.

record DynamicsCollapseDepth
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    attractorSurface :
      DFPU.DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    collapseDepth :
      PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence attractorSurface)) →
      Nat

    collapseDepthWitness :
      (s : PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence attractorSurface))) →
      DSC.iterate (collapseDepth s)
        (PGFG.evolve
          (DSC.flowGap
            (DFPU.stepCoherence attractorSurface)))
        s
        ≡
      PGFG.heldPoint
        (DSC.flowGap
          (DFPU.stepCoherence attractorSurface))

    nonClaimBoundary : List String

open DynamicsCollapseDepth public

mkDynamicsCollapseDepth :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (attractorSurface :
    DFPU.DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (collapseDepth :
    PGFG.FlowState
      (DSC.flowGap
        (DFPU.stepCoherence attractorSurface)) →
    Nat) →
  ((s : PGFG.FlowState
    (DSC.flowGap
      (DFPU.stepCoherence attractorSurface))) →
    DSC.iterate (collapseDepth s)
      (PGFG.evolve
        (DSC.flowGap
          (DFPU.stepCoherence attractorSurface)))
      s
      ≡
    PGFG.heldPoint
      (DSC.flowGap
        (DFPU.stepCoherence attractorSurface))) →
  DynamicsCollapseDepth {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkDynamicsCollapseDepth attractorSurface collapseDepth collapseDepthWitness =
  record
    { attractorSurface = attractorSurface
    ; collapseDepth = collapseDepth
    ; collapseDepthWitness = collapseDepthWitness
    ; nonClaimBoundary =
        "DynamicsCollapseDepth is a bounded finite-carrier depth-to-held surface only"
        ∷ "collapseDepth is a supplied exact index on the current carrier"
        ∷ "collapseDepthWitness is an exact finite iteration witness, not a continuum time observable"
        ∷ "No metric, entropy, or physical clock claim is implied"
        ∷ DFPU.nonClaimBoundary attractorSurface
    }
