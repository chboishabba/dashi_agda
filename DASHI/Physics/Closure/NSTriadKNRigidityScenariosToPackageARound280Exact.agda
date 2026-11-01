module DASHI.Physics.Closure.NSTriadKNRigidityScenariosToPackageARound280Exact where

------------------------------------------------------------------------
-- ROUND280 / SCENARIO RIGIDITY -> LITERAL ROUND240 PACKAGE A
--
-- This is the backward consumer for R272--279.  It does not assume an ESS
-- theorem for every critical element.  Instead every bad sequence must produce
-- the SAME dynamic mixed-defect critical element, its maximal-lifespan
-- dynamics must fall into the R273 classification, and each scenario must be
-- impossible by the appropriate branch theorem:
--
--   global bounded frequency  -> R274 + R275;
--   global unbounded frequency -> corrected R277 persistence theorem;
--   finite terminal time       -> R278 + R279 ESS theorem.
--
-- Once all bad sequences are excluded, the already-merged R268 sequential
-- boundedness theorem constructs the literal R240 spacetime budget.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNSequentialUnboundednessUniformBoundRound268Exact as R268

F : C3.RealField _
F = Rational.rationalRealField

module ScenarioCompletion
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module H = R268.SequentialBoundedness Time initialTime integrateTo DerivativeOf

  record RigidityScenarioCompletion
      {ℓBad ℓDynamics : Level}
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      (BadSequence : Set ℓBad)
      (CriticalDynamics : Set ℓDynamics)
      : Set (lsuc (ℓBad ⊔ ℓDynamics)) where
    field
      badToSameDynamicCriticalElement : BadSequence → CriticalDynamics

      maximalLifespanScenarioClassification :
        (bad : BadSequence) → Set ℓDynamics

      boundedFrequencyScenarioImpossible :
        (bad : BadSequence) → Set ℓDynamics

      rapidCascadeScenarioImpossible :
        (bad : BadSequence) → Set ℓDynamics

      finiteTimeScenarioImpossibleByESS :
        (bad : BadSequence) → Set ℓDynamics

      classificationAndThreeRigidityBranchesExcludeBad :
        (bad : BadSequence) → ⊥

      sequentialBoundedness :
        H.ClassicalSequentialBoundednessInstance T BadSequence

  open RigidityScenarioCompletion public

  scenarioCompletionBuildsLiteralRound240PackageA :
    ∀ {ℓBad ℓDynamics}
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      {BadSequence : Set ℓBad}
      {CriticalDynamics : Set ℓDynamics} →
    RigidityScenarioCompletion T BadSequence CriticalDynamics →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  scenarioCompletionBuildsLiteralRound240PackageA T R =
    H.noBadSequenceBuildsPhysicalPackageA T
      (sequentialBoundedness R)
      (classificationAndThreeRigidityBranchesExcludeBad R)

round280ScenarioConsumerTargetsLiteralRound240Budget : Bool
round280ScenarioConsumerTargetsLiteralRound240Budget = true

round280NoNewPackageAProxy : Bool
round280NoNewPackageAProxy = true

round280PhysicalScenarioRigidityInstalled : Bool
round280PhysicalScenarioRigidityInstalled = false

round280PhysicalPackageAClosed : Bool
round280PhysicalPackageAClosed = false

round280ClayPromotion : Bool
round280ClayPromotion = false

round280PhysicalPackageAClosedIsFalse : round280PhysicalPackageAClosed ≡ false
round280PhysicalPackageAClosedIsFalse = refl
