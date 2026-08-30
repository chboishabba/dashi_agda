module DASHI.Physics.Closure.NSTriadKNPackageASequentialBoundRound258Exact where

------------------------------------------------------------------------
-- ROUND258 / NO BAD SEQUENCE -> AUTHORITATIVE ROUND240 PACKAGE-A BUDGET
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

module PackageASequential
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record SequentialUniformBoundAuthority
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      integratedMixedHelicityBound :
        (cutoff : Nat) (terminal : Time) →
        integrateTo (Dyn.mixedHelicityMass T cutoff) terminal
        ≤ cutoffIndependentBound terminal

  open SequentialUniformBoundAuthority public

  authorityBuildsPhysicalPackageA :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    SequentialUniformBoundAuthority T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  authorityBuildsPhysicalPackageA T A = record
    { Dyn.cutoffIndependentBound = cutoffIndependentBound A
    ; Dyn.integratedMixedHelicityBound = integratedMixedHelicityBound A
    }

round258AuthoritativeTargetIsRound240PhysicalBudget : Bool
round258AuthoritativeTargetIsRound240PhysicalBudget = true

round258NoNewPackageAProxyIntroduced : Bool
round258NoNewPackageAProxyIntroduced = true

round258SequentialBoundednessSelectionKernelDerivedHere : Bool
round258SequentialBoundednessSelectionKernelDerivedHere = false

round258PhysicalPackageACompilerClosed : Bool
round258PhysicalPackageACompilerClosed = true

round258ClayPromotion : Bool
round258ClayPromotion = false

round258PhysicalPackageACompilerClosedIsTrue :
  round258PhysicalPackageACompilerClosed ≡ true
round258PhysicalPackageACompilerClosedIsTrue = refl
