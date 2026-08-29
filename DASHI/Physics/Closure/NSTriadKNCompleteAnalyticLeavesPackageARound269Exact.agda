module DASHI.Physics.Closure.NSTriadKNCompleteAnalyticLeavesPackageARound269Exact where

------------------------------------------------------------------------
-- ROUND269 / CONDITIONAL A B C D* F G* H COMPILER -> LITERAL ROUND240 BUDGET
--
-- R263--R266 and R268 resolve the standard/source instances A, B, C, D*, H.
-- R267 deliberately leaves F/G* as one explicit conditional authority because
-- known GKP/ESS results do not automatically promote mixed-defect badness to
-- the required singular critical element / terminal-vorticity hypotheses.
--
-- Consequently this file is the exact FINAL COMPILER: once the two R270
-- research implications are proved on the same selected profile, the result
-- is the literal PhysicalNSMixedHelicitySpacetimeBudget, not another proxy.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc; _⊔_)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Data.Empty using (⊥)
open import Data.Rational.Base using (ℚ)

import DASHI.Physics.Closure.NSConcreteAubinLionsNonlinearLimitWitnesses as Concrete
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNRationalOrderedFiniteL2 as Rational
import DASHI.Physics.Closure.NSTriadKNPhysicalNSGalerkinTrajectoryRound240Exact as R240
import DASHI.Physics.Closure.NSTriadKNStandardSpacetimeW1AndFirstHitW3Round251Exact as R251
import DASHI.Physics.Closure.NSTriadKNPeriodicSobolevSpacetimeInstanceRound263Exact as R263
import DASHI.Physics.Closure.NSTriadKNCanonicalG2EnergyBalanceInstanceRound264Exact as R264
import DASHI.Physics.Closure.NSTriadKNFiniteDimensionalFirstHitInstanceRound265Exact as R265
import DASHI.Physics.Closure.NSTriadKNFirstHitPeriodicProfileInstanceRound266Exact as R266
import DASHI.Physics.Closure.NSTriadKNCriticalProfileSelectionESSInstanceRound267Exact as R267
import DASHI.Physics.Closure.NSTriadKNSequentialUnboundednessUniformBoundRound268Exact as R268

F : C3.RealField _
F = Rational.rationalRealField

module CompleteAnalyticLeaves
    {ℓState ℓProp ℓTorus ℓEuclid ℓProfile ℓBad : Level}
    (Time : Set)
    (initialTime : Time)
    (integrateTo : (Time → ℚ) → Time → ℚ)
    (DerivativeOf :
      (Time → C3.Complex3 F) →
      (Time → C3.Complex3 F) → Set)
    (S : Concrete.ConcreteGalerkinSetting ℓState ℓProp)
    (G2 : Concrete.G2ExactGalerkinEnergy S)
    (mixedMass criticalSize dissipationDensity : Nat → Time → ℚ)
    (Before : Time → Time → Set)
    (threshold : ℚ)
    (TorusState : Set ℓTorus)
    (EuclideanState : Set ℓEuclid)
    (stateAt : Nat → Time → TorusState)
    (Profile : Set ℓProfile)
    (BadSequence : Set ℓBad) where

  module Dyn = R240.PhysicalNSDynamics Time initialTime integrateTo DerivativeOf
  module H = R268.SequentialBoundedness Time initialTime integrateTo DerivativeOf

  record AllAnalyticInstances
      (T : Dyn.PhysicalNSGalerkinTrajectory)
      : Set (lsuc (ℓState ⊔ ℓProp ⊔ ℓTorus ⊔ ℓEuclid ⊔ ℓProfile ⊔ ℓBad)) where
    field
      leafA :
        R263.PeriodicSobolevSpacetimeInstance
          Time integrateTo mixedMass criticalSize dissipationDensity

      leafB :
        R264.CanonicalG2EnergyBalanceInstance
          S G2 Time
          (R251.integratedDissipation (R263.monotoneSpacetime leafA))

      leafCFromBad :
        BadSequence →
        R265.FiniteDimensionalFirstHitInstance
          Time Before criticalSize threshold

      leafDFromBad :
        (bad : BadSequence) →
        R266.FirstHitPeriodicProfileInstance
          Time criticalSize threshold
          (R265.buildActualFirstHitCriticalSequence (leafCFromBad bad))
          TorusState EuclideanState stateAt

      -- CONDITIONAL F/G*: R270 explains why known GKP/ESS theorems do not
      -- manufacture this field automatically from mixed-defect badness.
      leafFGFromBad :
        BadSequence →
        R267.CriticalProfileSelectionESSInstance Profile

      selectedCriticalProfileDescendsFromLeafD :
        (bad : BadSequence) → Set

      leafH :
        H.ClassicalSequentialBoundednessInstance T BadSequence

  open AllAnalyticInstances public

  badSequenceImpossible :
    ∀ {T : Dyn.PhysicalNSGalerkinTrajectory} →
    AllAnalyticInstances T → BadSequence → ⊥
  badSequenceImpossible A bad =
    R267.criticalSelectedProfileImpossible (leafFGFromBad A bad)

  allAnalyticLeavesBuildLiteralRound240Budget :
    (T : Dyn.PhysicalNSGalerkinTrajectory) →
    AllAnalyticInstances T →
    Dyn.PhysicalNSMixedHelicitySpacetimeBudget T
  allAnalyticLeavesBuildLiteralRound240Budget T A =
    H.noBadSequenceBuildsPhysicalPackageA T (leafH A)
      (badSequenceImpossible A)

round269ABCDstarHSourceInstancesResolved : Bool
round269ABCDstarHSourceInstancesResolved = true

round269ConditionalFGCompilerTargetsLiteralRound240Budget : Bool
round269ConditionalFGCompilerTargetsLiteralRound240Budget = true

round269PhysicalFGstarInstalled : Bool
round269PhysicalFGstarInstalled = false

round269PhysicalPackageAClosed : Bool
round269PhysicalPackageAClosed = false

round269NoNewPackageAProxy : Bool
round269NoNewPackageAProxy = true

round269ClayPromotion : Bool
round269ClayPromotion = false

round269ConditionalFGCompilerTargetsLiteralRound240BudgetIsTrue :
  round269ConditionalFGCompilerTargetsLiteralRound240Budget ≡ true
round269ConditionalFGCompilerTargetsLiteralRound240BudgetIsTrue = refl

round269PhysicalFGstarInstalledIsFalse :
  round269PhysicalFGstarInstalled ≡ false
round269PhysicalFGstarInstalledIsFalse = refl

round269PhysicalPackageAClosedIsFalse :
  round269PhysicalPackageAClosed ≡ false
round269PhysicalPackageAClosedIsFalse = refl
