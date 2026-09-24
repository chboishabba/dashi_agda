{-# OPTIONS --safe #-}
module DASHI.Physics.Closure.NSTriadKNLiveSelfMultiplierExternalSpacetimeRound628Exact where

------------------------------------------------------------------------
-- ROUND628 / LIVE SELF MULTIPLIER-DIFFERENCE + CANONICAL EXTERNAL -> R568
--
-- R627 puts the signed self spectator row on the literal four-helicity
-- multiplier-difference fold.  Lift that equality through the same beta/output
-- and time aggregation already used by R624.
--
-- The resulting least-privilege hard-side producer is:
--
--   cutoff-uniform signed bound on integrated self multiplier-difference rows
--   + cutoff-uniform signed bound on integrated canonical external rows
--       -> R624 SelfCanonicalExternalNestedSpacetimeBudget
--       -> R568 CommutatorOnlySpacetimeBudget568.
--
-- No positive majorant, norm, absolute value, or analytic estimate is supplied
-- here.  The two displayed signed inequalities remain the live PDE debt.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; 0ℚ; _+_; _*_; _≤_)
open import Relation.Binary.PropositionalEquality using (cong₂; subst)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNCanonicalCutoffSameObjectSystemRound34Exact as Canonical
import DASHI.Physics.Closure.NSTriadKNPhysicalTriadEnumeration as Physical
import DASHI.Physics.Closure.NSTriadKNPhysicalOutputFiber as Output
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNIntegrationTransportAuthorityRound495Exact as R495
import DASHI.Physics.Closure.NSTriadKNFactoredFullCommutatorOnlyRound567Exact as R567
import DASHI.Physics.Closure.NSTriadKNLiveCommutatorOnlyLeafABoundaryRound568Exact as R568
import DASHI.Physics.Closure.NSTriadKNLiveNestedSelfCanonicalExternalSpacetimeRound624Exact as R624
import DASHI.Physics.Closure.NSTriadKNSpectatorSelfMultiplierDifferenceRowRound627Exact as R627

F : C3.RealField _
F = Rational.rationalRealField

module LiveMultiplierExternal
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (integration : R495.IntegrationTransportAuthority Time integrateTo) where

  module Base = R624.LiveCanonicalSplit
    Time initialTime integrateTo DerivativeOf integration

  module Dyn = Base.Dyn
  module Support = Base.Support
  module Comm = Base.Comm

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (cutoff : Nat) (time : Time) where

    module A = Base.At T R cutoff time
    module MultiplierRows = R627.SpectatorSelfMultiplierRow
      A.B.Slice.PS A.B.S A.B.L A.B.H A.B.velocityTransverse

    selfMultiplierRows :
      Z3.FourierMode →
      List Physical.PhysicalTriadIncidence → ℚ
    selfMultiplierRows output [] = 0ℚ
    selfMultiplierRows output (beta ∷ rest) =
      MultiplierRows.selfMultiplierNestedForcingRow output beta
        + selfMultiplierRows output rest

    selfRowsAreMultiplierRows :
      (output : Z3.FourierMode) →
      (betas : List Physical.PhysicalTriadIncidence) →
      A.selfRows output betas
      ≡ selfMultiplierRows output betas
    selfRowsAreMultiplierRows output [] = refl
    selfRowsAreMultiplierRows output (beta ∷ rest) =
      cong₂ _+_
        (MultiplierRows.selfNestedForcingRowIsMultiplierDifference
          output beta)
        (selfRowsAreMultiplierRows output rest)

    selfMultiplierOutputForcingFull :
      Z3.FourierMode → ℚ
    selfMultiplierOutputForcingFull output =
      selfMultiplierRows output
        (Output.physicalOutputFiber cutoff output)

    selfNestedOutputIsMultiplierDifference :
      (output : Z3.FourierMode) →
      A.selfNestedOutputForcingFull output
      ≡ selfMultiplierOutputForcingFull output
    selfNestedOutputIsMultiplierDifference output =
      selfRowsAreMultiplierRows output
        (Output.physicalOutputFiber cutoff output)

  selfMultiplierSumOutputs :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) → Time → List Z3.FourierMode → ℚ
  selfMultiplierSumOutputs T R cutoff time [] = 0ℚ
  selfMultiplierSumOutputs T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    A.selfMultiplierOutputForcingFull output
      + selfMultiplierSumOutputs T R cutoff time rest

  selfNestedSumOutputsIsMultiplierDifference :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    (outputs : List Z3.FourierMode) →
    Base.selfNestedSumOutputs T R cutoff time outputs
    ≡ selfMultiplierSumOutputs T R cutoff time outputs
  selfNestedSumOutputsIsMultiplierDifference T R cutoff time [] = refl
  selfNestedSumOutputsIsMultiplierDifference
      T R cutoff time (output ∷ rest) =
    let module A = At T R cutoff time in
    cong₂ _+_
      (A.selfNestedOutputIsMultiplierDifference output)
      (selfNestedSumOutputsIsMultiplierDifference
        T R cutoff time rest)

  selfMultiplierGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  selfMultiplierGlobalForcingFull T R cutoff time =
    selfMultiplierSumOutputs T R cutoff time
      (Canonical.nonzeroCutoffModes cutoff)

  selfNestedGlobalIsMultiplierDifference :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (time : Time) →
    Base.selfNestedGlobalForcingFull T R cutoff time
    ≡ selfMultiplierGlobalForcingFull T R cutoff time
  selfNestedGlobalIsMultiplierDifference T R cutoff time =
    selfNestedSumOutputsIsMultiplierDifference
      T R cutoff time (Canonical.nonzeroCutoffModes cutoff)

  integratedSelfMultiplierGlobalForcingFull :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    Nat → Time → ℚ
  integratedSelfMultiplierGlobalForcingFull T R cutoff terminal =
    integrateTo (selfMultiplierGlobalForcingFull T R cutoff) terminal

  integratedSelfNestedIsMultiplierDifference :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    (R : Support.LiteralNonzeroCutoffTrajectory T) →
    (cutoff : Nat) (terminal : Time) →
    Base.integratedSelfNestedGlobalForcingFull T R cutoff terminal
    ≡ integratedSelfMultiplierGlobalForcingFull T R cutoff terminal
  integratedSelfNestedIsMultiplierDifference T R cutoff terminal =
    R495.integrateCongruent integration
      (Base.selfNestedGlobalForcingFull T R cutoff)
      (selfMultiplierGlobalForcingFull T R cutoff)
      (selfNestedGlobalIsMultiplierDifference T R cutoff)
      terminal

  record SelfMultiplierCanonicalExternalSpacetimeBudget
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T) : Set₁ where
    field
      selfMultiplierBound canonicalExternalBound : Time → ℚ

      selfMultiplierSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 *
          integratedSelfMultiplierGlobalForcingFull
            T R cutoff terminal
        ≤ selfMultiplierBound terminal

      canonicalExternalSignedBudget :
        (cutoff : Nat) (terminal : Time) →
        R567.four567 *
          Base.integratedCanonicalExternalNestedGlobalForcingFull
            T R cutoff terminal
        ≤ canonicalExternalBound terminal

  open SelfMultiplierCanonicalExternalSpacetimeBudget public

  multiplierExternalBudgetBuildsR624 :
    ∀ {T R} →
    SelfMultiplierCanonicalExternalSpacetimeBudget T R →
    Base.SelfCanonicalExternalNestedSpacetimeBudget T R
  multiplierExternalBudgetBuildsR624 {T} {R} B = record
    { Base.selfNestedBound = selfMultiplierBound B
    ; Base.canonicalExternalNestedBound = canonicalExternalBound B
    ; Base.selfNestedSignedBudget = λ cutoff terminal →
        subst
          (λ lhs → lhs ≤ selfMultiplierBound B terminal)
          (sym
            (cong₂ _*_
              refl
              (integratedSelfNestedIsMultiplierDifference
                T R cutoff terminal)))
          (selfMultiplierSignedBudget B cutoff terminal)
    ; Base.canonicalExternalNestedSignedBudget =
        canonicalExternalSignedBudget B
    }

  multiplierExternalBudgetBuildsR568 :
    ∀ {T R} →
    SelfMultiplierCanonicalExternalSpacetimeBudget T R →
    Comm.CommutatorOnlySpacetimeBudget568 T R
  multiplierExternalBudgetBuildsR568 B =
    Base.splitNestedBudgetBuildsR568
      (multiplierExternalBudgetBuildsR624 B)

------------------------------------------------------------------------
-- Status / frontier.
------------------------------------------------------------------------

round628LiveSelfMultiplierDifferenceSpacetimeWeldClosed : Bool
round628LiveSelfMultiplierDifferenceSpacetimeWeldClosed = true

round628SelfMultiplierPlusCanonicalExternalCompilesToR568 : Bool
round628SelfMultiplierPlusCanonicalExternalCompilesToR568 = true

round628SelfMultiplierSignedSpacetimeBudgetClosed : Bool
round628SelfMultiplierSignedSpacetimeBudgetClosed = false

round628CanonicalExternalSignedSpacetimeBudgetClosed : Bool
round628CanonicalExternalSignedSpacetimeBudgetClosed = false

round628IntroducesEstimate : Bool
round628IntroducesEstimate = false

round628ClayPromotion : Bool
round628ClayPromotion = false

round628LiveSelfMultiplierDifferenceSpacetimeWeldClosedIsTrue :
  round628LiveSelfMultiplierDifferenceSpacetimeWeldClosed ≡ true
round628LiveSelfMultiplierDifferenceSpacetimeWeldClosedIsTrue = refl

round628SelfMultiplierPlusCanonicalExternalCompilesToR568IsTrue :
  round628SelfMultiplierPlusCanonicalExternalCompilesToR568 ≡ true
round628SelfMultiplierPlusCanonicalExternalCompilesToR568IsTrue = refl

round628IntroducesEstimateIsFalse :
  round628IntroducesEstimate ≡ false
round628IntroducesEstimateIsFalse = refl

round628ClayPromotionIsFalse :
  round628ClayPromotion ≡ false
round628ClayPromotionIsFalse = refl
