module DASHI.Physics.DynamicsCollapseDepthMonotone where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (zero)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)
open import Data.Nat using (_≤_; _<_)
open import Relation.Nullary using (¬_)

open import DASHI.Physics.DynamicsCollapseDepth as DCD
open import DASHI.Physics.DynamicsFixedPointUniqueness as DFPU
open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Bounded monotone / strict-collapse law for a finite depth-to-held surface.
--
-- This module does not claim a metric contraction, smooth Lyapunov flow, or
-- continuum dissipation theorem. It only packages:
--   * one exact collapse-depth surface,
--   * one monotonicity witness under the current step,
--   * one strict-off-held witness,
--   * and one exact zero-depth witness at the held point.

record DynamicsCollapseDepthMonotone
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    depthSurface :
      DCD.DynamicsCollapseDepth {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    monotone :
      (s : PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface)))) →
      DCD.collapseDepth depthSurface
        (PGFG.evolve
          (DSC.flowGap
            (DFPU.stepCoherence
              (DCD.attractorSurface depthSurface)))
          s)
        ≤
      DCD.collapseDepth depthSurface s

    strictOffHeld :
      (s : PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface)))) →
      ¬ (s ≡ PGFG.heldPoint
            (DSC.flowGap
              (DFPU.stepCoherence
                (DCD.attractorSurface depthSurface)))) →
      DCD.collapseDepth depthSurface
        (PGFG.evolve
          (DSC.flowGap
            (DFPU.stepCoherence
              (DCD.attractorSurface depthSurface)))
          s)
        <
      DCD.collapseDepth depthSurface s

    fixedZero :
      DCD.collapseDepth depthSurface
        (PGFG.heldPoint
          (DSC.flowGap
            (DFPU.stepCoherence
              (DCD.attractorSurface depthSurface))))
        ≡ zero

    nonClaimBoundary : List String

open DynamicsCollapseDepthMonotone public

mkDynamicsCollapseDepthMonotone :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (depthSurface :
    DCD.DynamicsCollapseDepth {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  ((s : PGFG.FlowState
    (DSC.flowGap
      (DFPU.stepCoherence
        (DCD.attractorSurface depthSurface)))) →
    DCD.collapseDepth depthSurface
      (PGFG.evolve
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface)))
        s)
      ≤
    DCD.collapseDepth depthSurface s) →
  ((s : PGFG.FlowState
    (DSC.flowGap
      (DFPU.stepCoherence
        (DCD.attractorSurface depthSurface)))) →
    ¬ (s ≡ PGFG.heldPoint
          (DSC.flowGap
            (DFPU.stepCoherence
              (DCD.attractorSurface depthSurface)))) →
    DCD.collapseDepth depthSurface
      (PGFG.evolve
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface)))
        s)
      <
    DCD.collapseDepth depthSurface s) →
  (DCD.collapseDepth depthSurface
    (PGFG.heldPoint
      (DSC.flowGap
        (DFPU.stepCoherence
          (DCD.attractorSurface depthSurface))))
    ≡ zero) →
  DynamicsCollapseDepthMonotone {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkDynamicsCollapseDepthMonotone depthSurface monotone strictOffHeld fixedZero =
  record
    { depthSurface = depthSurface
    ; monotone = monotone
    ; strictOffHeld = strictOffHeld
    ; fixedZero = fixedZero
    ; nonClaimBoundary =
        "DynamicsCollapseDepthMonotone is a bounded finite-carrier order surface only"
        ∷ "monotone and strictOffHeld are supplied exact witnesses on the current carrier"
        ∷ "fixedZero is an exact normalization at the held point"
        ∷ "No metric contraction, entropy law, or physical arrow-of-time claim is implied"
        ∷ DCD.nonClaimBoundary depthSurface
    }
