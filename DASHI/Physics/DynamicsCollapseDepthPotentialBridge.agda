module DASHI.Physics.DynamicsCollapseDepthPotentialBridge where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DynamicsCollapseDepth as DCD
open import DASHI.Physics.DynamicsFixedPointUniqueness as DFPU
open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Bounded exact agreement surface between collapse depth and a Nat-valued
-- potential on the same finite carrier.
--
-- This module does not claim a canonical energy, entropy, or MDL equivalence
-- theorem. It only packages:
--   * one finite-carrier collapse-depth surface,
--   * one Nat-valued potential on the same carrier,
--   * and one exact pointwise agreement witness.

record DynamicsCollapseDepthPotentialBridge
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    depthSurface :
      DCD.DynamicsCollapseDepth {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    potential :
      PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface))) →
      Nat

    agreement :
      (s : PGFG.FlowState
        (DSC.flowGap
          (DFPU.stepCoherence
            (DCD.attractorSurface depthSurface)))) →
      DCD.collapseDepth depthSurface s ≡ potential s

    nonClaimBoundary : List String

open DynamicsCollapseDepthPotentialBridge public

mkDynamicsCollapseDepthPotentialBridge :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (depthSurface :
    DCD.DynamicsCollapseDepth {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (potential :
    PGFG.FlowState
      (DSC.flowGap
        (DFPU.stepCoherence
          (DCD.attractorSurface depthSurface))) →
    Nat) →
  ((s : PGFG.FlowState
    (DSC.flowGap
      (DFPU.stepCoherence
        (DCD.attractorSurface depthSurface)))) →
    DCD.collapseDepth depthSurface s ≡ potential s) →
  DynamicsCollapseDepthPotentialBridge {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkDynamicsCollapseDepthPotentialBridge depthSurface potential agreement =
  record
    { depthSurface = depthSurface
    ; potential = potential
    ; agreement = agreement
    ; nonClaimBoundary =
        "DynamicsCollapseDepthPotentialBridge is a bounded finite-carrier agreement surface only"
        ∷ "potential is a supplied Nat-valued scalar on the current carrier"
        ∷ "agreement is an exact pointwise witness, not a general MDL, entropy, or energy theorem"
        ∷ "No continuum thermodynamic or physical-energy claim is implied"
        ∷ DCD.nonClaimBoundary depthSurface
    }
