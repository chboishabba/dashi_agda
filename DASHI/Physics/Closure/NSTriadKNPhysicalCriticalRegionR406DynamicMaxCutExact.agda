module DASHI.Physics.Closure.NSTriadKNPhysicalCriticalRegionR406DynamicMaxCutExact where

------------------------------------------------------------------------
-- POSITIVE B7 / EXACT DYNAMIC RECUT OF THE LITERAL R406 REMAINDER
--
-- The universal pointwise identification of the quintic R406 remainder with a
-- quartic coherent covariance is ruled out by the homogeneity audit.  The live
-- R406 owner already supplies the correct dynamic same-object identity on its
-- fixed canonical output list:
--
--   canonicalDebt = - offDiagonalFluxTangent + weightedRemainder.
--
-- Pure rational algebra therefore gives, on the SAME literal R406 carrier,
--
--   weightedRemainder = canonicalDebt + offDiagonalFluxTangent.
--
-- This is the correct exact replacement for the rejected degree-mismatched
-- equality.  No estimate or integration is introduced.  The remaining B7
-- work is now split honestly into:
--
--   (1) prove the stored flux tangent is the actual time derivative and turn it
--       into an endpoint term under integration;
--   (2) pay the resulting quartic canonical Gram debt in the positive-B
--       currency (or provide another quantitative R406 transport).
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _+_)
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNLiteralCutoffTrajectorySupportRound405Exact as R405
import DASHI.Physics.Closure.NSTriadKNFixedOutputLiveGlobalFluxRound406Exact as R406

F : C3.RealField _
F = Rational.rationalRealField

module DynamicR406
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Support = R405.LiteralCutoffSupport
    Time initialTime integrateTo DerivativeOf
  module Fixed = R406.FixedLiveFlux
    Time initialTime integrateTo DerivativeOf

  module At
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (R : Support.LiteralNonzeroCutoffTrajectory T)
      (N : Nat) (t : Time) where

    module Live = Fixed.At T R N t

    /-- Exact dynamic normal form for the SAME literal R406 weighted remainder. -/
    weightedRemainderIsDebtPlusFluxTangent :
      Live.weightedRemainder
      ≡ Live.canonicalDebt + Live.offDiagonalFluxTangent
    weightedRemainderIsDebtPlusFluxTangent =
      let
        shifted :
          Live.canonicalDebt + Live.offDiagonalFluxTangent
          ≡ ((0ℚ - Live.offDiagonalFluxTangent) + Live.weightedRemainder)
              + Live.offDiagonalFluxTangent
        shifted =
          cong (_+ Live.offDiagonalFluxTangent)
            Live.canonicalDebtFluxIdentity

        reduced :
          ((0ℚ - Live.offDiagonalFluxTangent) + Live.weightedRemainder)
              + Live.offDiagonalFluxTangent
          ≡ Live.weightedRemainder
        reduced =
          solve (Live.offDiagonalFluxTangent ∷ Live.weightedRemainder ∷ [])
      in
      sym (trans shifted reduced)

------------------------------------------------------------------------
-- Status / new true cut.
------------------------------------------------------------------------

b7R406DebtPlusFluxTangentDecompositionClosed : Bool
b7R406DebtPlusFluxTangentDecompositionClosed = true

b7RejectedUniversalCovarianceEqualityNeeded : Bool
b7RejectedUniversalCovarianceEqualityNeeded = false

b7ActualFluxDerivativeClosed : Bool
b7ActualFluxDerivativeClosed = R406.round406ActualTimeDerivativeOfFluxProved

b7QuarticGramDebtPaymentClosed : Bool
b7QuarticGramDebtPaymentClosed = false

b7DynamicSpacetimeTransportClosed : Bool
b7DynamicSpacetimeTransportClosed = false

b7IntroducesEstimate : Bool
b7IntroducesEstimate = false

clayPromotion : Bool
clayPromotion = false

b7R406DebtPlusFluxTangentDecompositionClosedIsTrue :
  b7R406DebtPlusFluxTangentDecompositionClosed ≡ true
b7R406DebtPlusFluxTangentDecompositionClosedIsTrue = refl

b7RejectedUniversalCovarianceEqualityNeededIsFalse :
  b7RejectedUniversalCovarianceEqualityNeeded ≡ false
b7RejectedUniversalCovarianceEqualityNeededIsFalse = refl

b7ActualFluxDerivativeClosedIsFalse :
  b7ActualFluxDerivativeClosed ≡ false
b7ActualFluxDerivativeClosedIsFalse = refl

b7QuarticGramDebtPaymentClosedIsFalse :
  b7QuarticGramDebtPaymentClosed ≡ false
b7QuarticGramDebtPaymentClosedIsFalse = refl
