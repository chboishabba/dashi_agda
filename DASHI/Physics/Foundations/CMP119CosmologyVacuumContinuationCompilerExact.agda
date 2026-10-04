{-# OPTIONS --safe #-}
module DASHI.Physics.Foundations.CMP119CosmologyVacuumContinuationCompilerExact where

------------------------------------------------------------------------
-- SELECTED FINITE WEYL RESPONSE -> LORENTZIAN VACUUM ACTIVE-STRESS SIGN.
--
-- This is deliberately a compiler, not a source producer.
--
-- Upstream now computes a selected finite Euclidean one-point Weyl response
-- from the SAME CMP119 density / finite measure / R144 complete action.
-- The only new physical premise exposed here is the continuation statement:
-- that this selected finite/renormalized trace is the trace of a Lorentzian
-- vacuum-like tensor on the SAME state.
--
-- Once that premise is inhabited, no independent local T00 upper bound is
-- needed: p = -rho gives Active = Theta/2 algebraically (equivalently
-- Theta = 2 Active), and positive rho forces Active < 0.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_)
open import Data.Rational.Base using (ℚ; 0ℚ; _<_)
open import Relation.Binary.PropositionalEquality using (subst; sym; trans)

import DASHI.Physics.Foundations.CMP119CosmologyVacuumTraceActiveCollapseExact as Vacuum

record SelectedVacuumContinuationWeld : Set where
  field
    selectedFiniteEuclideanWeylResponse : ℚ

    lorentzianVacuumStress :
      Vacuum.VacuumLikeLorentzianStress

    sameObjectTraceContinuation :
      Vacuum.trace
        (Vacuum.stress lorentzianVacuumStress)
      ≡
      selectedFiniteEuclideanWeylResponse

open SelectedVacuumContinuationWeld public

continuedLorentzianTrace :
  SelectedVacuumContinuationWeld → ℚ
continuedLorentzianTrace weld =
  Vacuum.trace (Vacuum.stress (lorentzianVacuumStress weld))

continuedLorentzianActiveStress :
  SelectedVacuumContinuationWeld → ℚ
continuedLorentzianActiveStress weld =
  Vacuum.activeStress (Vacuum.stress (lorentzianVacuumStress weld))

continuedTraceIsSelectedFiniteWeylResponse :
  ∀ weld →
  continuedLorentzianTrace weld
  ≡ selectedFiniteEuclideanWeylResponse weld
continuedTraceIsSelectedFiniteWeylResponse =
  sameObjectTraceContinuation

continuedVacuumTraceIsTwiceActive :
  ∀ weld →
  continuedLorentzianTrace weld
  ≡
  continuedLorentzianActiveStress weld
  + continuedLorentzianActiveStress weld
continuedVacuumTraceIsTwiceActive weld =
  Vacuum.vacuumTraceIsTwiceActive
    (lorentzianVacuumStress weld)

continuedVacuumPositiveRhoClosesNegativeActive :
  ∀ weld →
  0ℚ <
    Vacuum.rho
      (Vacuum.stress (lorentzianVacuumStress weld)) →
  continuedLorentzianActiveStress weld < 0ℚ
continuedVacuumPositiveRhoClosesNegativeActive weld positiveRho =
  Vacuum.vacuumPositiveRhoImpliesActiveNegative
    (lorentzianVacuumStress weld)
    positiveRho

continuedVacuumPositiveRhoClosesNegativeTrace :
  ∀ weld →
  0ℚ <
    Vacuum.rho
      (Vacuum.stress (lorentzianVacuumStress weld)) →
  selectedFiniteEuclideanWeylResponse weld < 0ℚ
continuedVacuumPositiveRhoClosesNegativeTrace weld positiveRho =
  subst
    (λ value → value < 0ℚ)
    (sameObjectTraceContinuation weld)
    (Vacuum.vacuumPositiveRhoImpliesTraceNegative
      (lorentzianVacuumStress weld)
      positiveRho)

------------------------------------------------------------------------
-- FRONTIER FLAGS
------------------------------------------------------------------------

negativeTraceAloneClosesGenericStateActiveStress : Bool
negativeTraceAloneClosesGenericStateActiveStress = false

vacuumSameObjectContinuationRemovesIndependentT00Bound : Bool
vacuumSameObjectContinuationRemovesIndependentT00Bound = true

selectedCMP119VacuumContinuationWeldStillOpen : Bool
selectedCMP119VacuumContinuationWeldStillOpen = true
