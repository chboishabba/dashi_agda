module DASHI.Physics.Closure.NSTriadKNBidiCriticalElementPackageARound259Exact where

------------------------------------------------------------------------
-- ROUND259 / COMPLETE BIDI LOGICAL SPINE TO THE AUTHORITATIVE PACKAGE-A BUDGET
--
-- Correct polarity:
--   bad unbounded cutoff sequence
--     -> selected first-hit/profile critical element
--     -> rigidity contradiction.
-- Hence no bad sequence exists.  A separately owned sequential boundedness
-- principle converts that negation into the literal Round240 physical budget.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)
open import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier using (Complex3)
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNCriticalElementBackwardUniquenessRound257Exact as R257
import DASHI.Physics.Closure.NSTriadKNPackageASequentialBoundRound258Exact as R258

F = Rational.rationalRealField

module CompleteBidi
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → Complex3 F) →
      (Time → Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module Pkg = R258.PackageASequential Time initialTime integrateTo DerivativeOf

  record BadSequenceCriticalElementLane
      {ℓBad ℓCritical : Level}
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (BadSequence : Set ℓBad)
      (CriticalElement : Set ℓCritical)
      : Set (lsuc (ℓBad ⊔ ℓCritical)) where
    field
      badToCriticalElement : BadSequence → CriticalElement
      rigidityFor :
        CriticalElement → R257.CriticalElementRigidityAuthority CriticalElement

  open BadSequenceCriticalElementLane public

  badSequenceImpossible :
    ∀ {ℓBad ℓCritical}
      {T : Dyn.PhysicalNSGalerkinTrajectory}
      {BadSequence : Set ℓBad}
      {CriticalElement : Set ℓCritical} →
    BadSequenceCriticalElementLane T BadSequence CriticalElement →
    BadSequence → ⊥
  badSequenceImpossible L bad =
    R257.criticalElementImpossible
      (rigidityFor L (badToCriticalElement L bad))

  record NoBadSequenceToPhysicalBudget
      {ℓBad : Level}
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (BadSequence : Set ℓBad) : Set (lsuc ℓBad) where
    field
      boundednessFromNoBadSequence :
        (BadSequence → ⊥) →
        Pkg.SequentialUniformBoundAuthority T

  open NoBadSequenceToPhysicalBudget public

  completeBidiLaneBuildsPackageA :
    ∀ {ℓBad ℓCritical}
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      {BadSequence : Set ℓBad}
      {CriticalElement : Set ℓCritical} →
    (L : BadSequenceCriticalElementLane T BadSequence CriticalElement) →
    NoBadSequenceToPhysicalBudget T BadSequence →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  completeBidiLaneBuildsPackageA T L B =
    Pkg.authorityBuildsPhysicalPackageA T
      (boundednessFromNoBadSequence B (badSequenceImpossible L))

round259BadSequenceContradictionPolarityCorrect : Bool
round259BadSequenceContradictionPolarityCorrect = true

round259TargetIsLiteralRound240PackageA : Bool
round259TargetIsLiteralRound240PackageA = true

round259CompilerAfterAnalyticAuthoritiesClosed : Bool
round259CompilerAfterAnalyticAuthoritiesClosed = true

round259AnalyticProfileRigidityAndBoundednessKernelDerivedHere : Bool
round259AnalyticProfileRigidityAndBoundednessKernelDerivedHere = false

round259ClayPromotion : Bool
round259ClayPromotion = false

round259CompilerAfterAnalyticAuthoritiesClosedIsTrue :
  round259CompilerAfterAnalyticAuthoritiesClosed ≡ true
round259CompilerAfterAnalyticAuthoritiesClosedIsTrue = refl
