module DASHI.Physics.DynamicsFixedPointUniqueness where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_)
open import Agda.Builtin.Nat using (Nat; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.DynamicsStepCoherence as DSC
open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Bounded unique-fixed-point / global-attractor surface over a finite flow gap.
--
-- This module still does not claim a general fixed-point theorem, contractive
-- metric structure, or continuum attractor theory. It only packages:
--   * one bounded step-coherence surface,
--   * one exact unique-fixed-point witness on the supplied carrier,
--   * and the derived finite-carrier fact that every iterate from step 2
--     onward lands at the same held point.

record DynamicsFixedPointUniqueness
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    stepCoherence :
      DSC.DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    uniqueFixedPoint :
      (s : PGFG.FlowState (DSC.flowGap stepCoherence)) →
      PGFG.evolve (DSC.flowGap stepCoherence) s ≡ s →
      s ≡ PGFG.heldPoint (DSC.flowGap stepCoherence)

    nonClaimBoundary : List String

open DynamicsFixedPointUniqueness public

fixed-is-held :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (uniqueness : DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (s : PGFG.FlowState (DSC.flowGap (stepCoherence uniqueness))) →
  PGFG.evolve (DSC.flowGap (stepCoherence uniqueness)) s ≡ s →
  s ≡ PGFG.heldPoint (DSC.flowGap (stepCoherence uniqueness))
fixed-is-held uniqueness =
  uniqueFixedPoint uniqueness

iterate-from-2-global-attractor :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (uniqueness : DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (n : Nat) →
  (s : PGFG.FlowState (DSC.flowGap (stepCoherence uniqueness))) →
  DSC.iterate (suc (suc n))
    (PGFG.evolve (DSC.flowGap (stepCoherence uniqueness)))
    s
    ≡
  PGFG.heldPoint (DSC.flowGap (stepCoherence uniqueness))
iterate-from-2-global-attractor uniqueness =
  DSC.iterate-from-2-held (stepCoherence uniqueness)

mkDynamicsFixedPointUniqueness :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (stepCoherence :
    DSC.DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  ((s : PGFG.FlowState (DSC.flowGap stepCoherence)) →
    PGFG.evolve (DSC.flowGap stepCoherence) s ≡ s →
    s ≡ PGFG.heldPoint (DSC.flowGap stepCoherence)) →
  DynamicsFixedPointUniqueness {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkDynamicsFixedPointUniqueness stepCoherence uniqueFixedPoint =
  record
    { stepCoherence = stepCoherence
    ; uniqueFixedPoint = uniqueFixedPoint
    ; nonClaimBoundary =
        "DynamicsFixedPointUniqueness is a bounded finite-carrier attractor surface only"
        ∷ "uniqueFixedPoint is a supplied exact witness on the current carrier"
        ∷ "iterate-from-2-global-attractor is a derived finite iteration fact, not a continuum attractor theorem"
        ∷ "No contractive metric, general semigroup, or asymptotic physical-law claim is implied"
        ∷ DSC.nonClaimBoundary stepCoherence
    }
