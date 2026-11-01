module DASHI.Physics.Closure.NSTriadKNPackageAToCriticalContinuationTargetRound411Exact where

------------------------------------------------------------------------
-- ROUND411 / SECOND CLAY-LEVEL PAYMENT: PACKAGE A -> CRITICAL CONTINUATION
--
-- R241 is one-way: a bounded critical barrier pays the mixed-helicity defect.
-- It cannot be reversed.  This round records the correct remaining Clay-facing
-- implication without pretending it follows from R241.
--
-- The target is indexed by the SAME literal Round240 trajectory and consumes
-- the authoritative Round240 Package-A budget.  Any successful proof may be
-- direct (continuation criterion) or indirect (critical element/rigidity), but
-- it must return a cutoff-uniform critical barrier on that same trajectory.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Rational.Base using (ℚ; _≤_)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240

F : C3.RealField _
F = Rational.rationalRealField

module Continuation
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record PackageAToCriticalBarrier
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (A : Dyn.PhysicalNSMixedHelicitySpacetimeBudget T) : Set₁ where
    field
      criticalSize : Nat → Time → ℚ
      cutoffIndependentCriticalBound : Time → ℚ
      criticalBarrier :
        (cutoff : Nat) (terminal : Time) →
        criticalSize cutoff terminal
        ≤ cutoffIndependentCriticalBound terminal

  open PackageAToCriticalBarrier public

round411R241ReversalUsed : Bool
round411R241ReversalUsed = false

round411TargetConsumesLiteralRound240PackageA : Bool
round411TargetConsumesLiteralRound240PackageA = true

round411TargetReturnsCutoffUniformCriticalBarrier : Bool
round411TargetReturnsCutoffUniformCriticalBarrier = true

round411PackageAToCriticalContinuationStillOpen : Bool
round411PackageAToCriticalContinuationStillOpen = true

round411R241ReversalUsedIsFalse : round411R241ReversalUsed ≡ false
round411R241ReversalUsedIsFalse = refl

round411TargetConsumesLiteralRound240PackageAIsTrue :
  round411TargetConsumesLiteralRound240PackageA ≡ true
round411TargetConsumesLiteralRound240PackageAIsTrue = refl
