module DASHI.Physics.DynamicsStepCoherence where

open import Agda.Primitive using (Level; Setω)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_)

open import DASHI.Physics.PressureGradientFlowGap as PGFG

------------------------------------------------------------------------
-- Bounded step-composition / closure surface over a finite flow gap.
--
-- This module still does not claim a general semigroup, continuous-time
-- flow, or asymptotic dynamical-systems theorem. It only packages:
--   * one exact held-point stability witness,
--   * the existing exact two-step absorption witness,
--   * and the derived fact that a third step remains at the held point.

record DynamicsStepCoherence
  {ℓs ℓp ℓo ℓq ℓr : Level}
  (V : Set)
  : Setω where
  field
    flowGap :
      PGFG.PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V

    heldStable :
      PGFG.evolve flowGap (PGFG.heldPoint flowGap)
        ≡
      PGFG.heldPoint flowGap

    nonClaimBoundary : List String

open DynamicsStepCoherence public

iterate :
  {A : Set} →
  Nat →
  (A → A) →
  A →
  A
iterate zero f x = x
iterate (suc n) f x = iterate n f (f x)

step²-to-held :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (coherence : DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (s : PGFG.FlowState (flowGap coherence)) →
  PGFG.evolve (flowGap coherence)
    (PGFG.evolve (flowGap coherence) s)
    ≡
  PGFG.heldPoint (flowGap coherence)
step²-to-held coherence =
  PGFG.evolutionCoherence (flowGap coherence)

step³-to-held :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (coherence : DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (s : PGFG.FlowState (flowGap coherence)) →
  PGFG.evolve (flowGap coherence)
    (PGFG.evolve (flowGap coherence)
      (PGFG.evolve (flowGap coherence) s))
    ≡
  PGFG.heldPoint (flowGap coherence)
step³-to-held coherence s
  rewrite step²-to-held coherence s
        | heldStable coherence
  = refl

held-absorbs-double-step :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (coherence : DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  PGFG.evolve (flowGap coherence)
    (PGFG.evolve (flowGap coherence)
      (PGFG.heldPoint (flowGap coherence)))
    ≡
  PGFG.heldPoint (flowGap coherence)
held-absorbs-double-step coherence =
  step²-to-held coherence (PGFG.heldPoint (flowGap coherence))

iterate-from-2-held :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (coherence : DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (n : Nat) →
  (s : PGFG.FlowState (flowGap coherence)) →
  iterate (suc (suc n))
    (PGFG.evolve (flowGap coherence))
    s
    ≡
  PGFG.heldPoint (flowGap coherence)
iterate-from-2-held coherence zero s =
  step²-to-held coherence s
iterate-from-2-held coherence (suc n) s
  rewrite iterate-from-2-held coherence n
    (PGFG.evolve (flowGap coherence) s)
        | heldStable coherence
  = refl

mkDynamicsStepCoherence :
  ∀ {ℓs ℓp ℓo ℓq ℓr V} →
  (flowGap :
    PGFG.PressureGradientFlowGap {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V) →
  (PGFG.evolve flowGap (PGFG.heldPoint flowGap) ≡ PGFG.heldPoint flowGap) →
  DynamicsStepCoherence {ℓs} {ℓp} {ℓo} {ℓq} {ℓr} V
mkDynamicsStepCoherence flowGap heldStable =
  record
    { flowGap = flowGap
    ; heldStable = heldStable
    ; nonClaimBoundary =
        "DynamicsStepCoherence is a bounded finite-carrier closure surface only"
        ∷ "heldStable is an exact held-point witness on the supplied carrier"
        ∷ "step²-to-held, step³-to-held, and iterate-from-2-held are exact finite iteration facts, not a global semigroup theorem"
        ∷ "No continuous-time flow, continuum limit, or asymptotic dynamical-systems claim is implied"
        ∷ PGFG.nonClaimBoundary flowGap
    }
