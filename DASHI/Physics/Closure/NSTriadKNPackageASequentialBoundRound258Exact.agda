module DASHI.Physics.Closure.NSTriadKNPackageASequentialBoundRound258Exact where

------------------------------------------------------------------------
-- ROUND258 / NO BAD SEQUENCE -> AUTHORITATIVE ROUND240 PACKAGE-A BUDGET
--
-- The target is not a new Package-A proxy.  It is exactly
--   R240.PhysicalNSMixedHelicitySpacetimeBudget T.
--
-- A critical-element contradiction excludes every unbounded bad cutoff
-- sequence.  The remaining functional-analysis step is the standard
-- sequential characterization of boundedness: if no sequence escapes every
-- finite bound, there is a finite cutoff-independent bound.  That selection
-- principle is source-owned here; the compiler into the exact R240 budget is
-- theoremised below.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; _≤_)
open import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier using (Complex3)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240

F = Rational.rationalRealField

module PackageASequential
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → Complex3 F) →
      (Time → Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf

  record SequentialUniformBoundAuthority
      (T : Dyn.PhysicalNSGalerkinTrajectory) : Set₁ where
    field
      cutoffIndependentBound : Time → ℚ
      integratedMixedHelicityBound :
        (cutoff : Agda.Builtin.Nat.Nat) (terminal : Time) →
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
