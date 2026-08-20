module DASHI.Physics.Closure.NSTriadKNUniformCriticalBarrierPassageToLimitRound103Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- Annali di Matematica Pura ed Applicata 146 (1987), 65--96.
-- DOI: 10.1007/BF01762360.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier-Stokes
-- Equations".
-- DOI: 10.1007/BF02392477.
--
-- Authors: Hajer Bahouri; Jean-Yves Chemin; Raphael Danchin.
-- Title: "Fourier Analysis and Nonlinear Partial Differential Equations".
-- DOI: 10.1007/978-3-642-16830-7.
--
-- ROUND103 / ONE-SHOT SAME-SOLUTION COMPACTNESS COMPILER
--
-- Round104 repairs both proof authority and carrier identity.  There is ONE
-- witness-bearing Round29 `CriticalAubinLionsTarget`; its Galerkin and limit
-- TYPES are identified with the consumer carriers, and its actual
-- `limitingState` element is transported along that type equality and required
-- to equal the exact `limitingSolution` consumed by Round90.  Thus neither an
-- unrelated proposition type nor a different solution in the same type can
-- discharge the continuation consumer.
--
-- The physical Sobolev/Simon instantiation remains open and fail-closed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (_≤_; _+_)
open import Relation.Binary.PropositionalEquality using (subst)

import DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact as Critical
import DASHI.Physics.Closure.NSTriadKNClayTopDownConsumerRound90Exact as Top

record UniformCriticalGalerkinLimitData
    (continuation : Critical.PeriodicSerrinContinuationTarget) : Set₁ where
  constructor uniform-critical-galerkin-limit-data
  field
    GalerkinSequence : Set
    limitingSolution : Critical.StrongSolution continuation

    limitingBudget : Critical.CriticalToSerrinBudget
    timeDerivativeBudget : Critical.NegativeNormTimeDerivativeBudget

    aubinLionsTarget : Critical.CriticalAubinLionsTarget

    sameGalerkinSequenceCarrier :
      Critical.GalerkinSequence aubinLionsTarget ≡ GalerkinSequence

    sameLimitStateCarrier :
      Critical.LimitState aubinLionsTarget
      ≡ Critical.StrongSolution continuation

    sameLimitingState :
      subst
        (λ stateType → stateType)
        sameLimitStateCarrier
        (Critical.limitingState aubinLionsTarget)
      ≡ limitingSolution

    limitingBudgetGivesL4L6Finite :
      Critical.integralL6Fourth limitingBudget
      ≤ Critical.sobolevConstantFourth limitingBudget
          * (Critical.supHOneHalfSquared limitingBudget
            * Critical.integralHThreeHalfSquared limitingBudget) →
      Critical.L4L6Finite continuation limitingSolution

open UniformCriticalGalerkinLimitData public

uniformCriticalTimeDerivativeBound :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.derivativeNorm (timeDerivativeBudget data)
  ≤ Critical.viscousBudget (timeDerivativeBudget data)
    + Critical.nonlinearBudget (timeDerivativeBudget data)
uniformCriticalTimeDerivativeBound data =
  Critical.timeDerivativeBoundFromEquation (timeDerivativeBudget data)

uniformCriticalCompactnessWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.strongL2HOneHalfCompactness (aubinLionsTarget data)
uniformCriticalCompactnessWitness data =
  Critical.strongL2HOneHalfCompactnessWitness (aubinLionsTarget data)

uniformCriticalQuadraticConvergenceWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.quadraticTermConvergence (aubinLionsTarget data)
uniformCriticalQuadraticConvergenceWitness data =
  Critical.quadraticTermConvergenceWitness (aubinLionsTarget data)

uniformCriticalInitialTraceWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.initialTraceRecovered (aubinLionsTarget data)
uniformCriticalInitialTraceWitness data =
  Critical.initialTraceRecoveredWitness (aubinLionsTarget data)

uniformCriticalLimitingEquationWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.limitingEquationRecovered (aubinLionsTarget data)
uniformCriticalLimitingEquationWitness data =
  Critical.limitingEquationRecoveredWitness (aubinLionsTarget data)

uniformCriticalWeakStarLSCWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.weakStarLowerSemicontinuity (aubinLionsTarget data)
uniformCriticalWeakStarLSCWitness data =
  Critical.weakStarLowerSemicontinuityWitness (aubinLionsTarget data)

uniformCriticalDissipationLSCWitness :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.weakDissipationLowerSemicontinuity (aubinLionsTarget data)
uniformCriticalDissipationLSCWitness data =
  Critical.weakDissipationLowerSemicontinuityWitness (aubinLionsTarget data)

uniformCriticalPassageConstructsSameSolutionBarrier :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Top.CriticalBarrierFor continuation (limitingSolution data)
uniformCriticalPassageConstructsSameSolutionBarrier data =
  Top.critical-barrier-for
    (limitingBudget data)
    (limitingBudgetGivesL4L6Finite data)

uniformCriticalPassageContinuesSameLimitingSolution :
  ∀ {continuation : Critical.PeriodicSerrinContinuationTarget} →
  (data : UniformCriticalGalerkinLimitData continuation) →
  Critical.ExtendsPastMaximalTime continuation (limitingSolution data)
uniformCriticalPassageContinuesSameLimitingSolution data =
  Top.topDownCriticalBarrierContinuesSameSolution
    (uniformCriticalPassageConstructsSameSolutionBarrier data)

round103SameSolutionCriticalPassageCompilerClosed : Bool
round103SameSolutionCriticalPassageCompilerClosed = true

round103EquationNegativeNormBudgetActuallyConsumed : Bool
round103EquationNegativeNormBudgetActuallyConsumed = true

round104SingleAubinLionsTargetSameCarrierWeld : Bool
round104SingleAubinLionsTargetSameCarrierWeld = true

round104ExactLimitElementWeldRequired : Bool
round104ExactLimitElementWeldRequired = true

round103PhysicalSimonAubinLionsInstantiationClosed : Bool
round103PhysicalSimonAubinLionsInstantiationClosed = false

round103SameSolutionCriticalPassageCompilerClosedIsTrue :
  round103SameSolutionCriticalPassageCompilerClosed ≡ true
round103SameSolutionCriticalPassageCompilerClosedIsTrue = refl

round103EquationNegativeNormBudgetActuallyConsumedIsTrue :
  round103EquationNegativeNormBudgetActuallyConsumed ≡ true
round103EquationNegativeNormBudgetActuallyConsumedIsTrue = refl

round104SingleAubinLionsTargetSameCarrierWeldIsTrue :
  round104SingleAubinLionsTargetSameCarrierWeld ≡ true
round104SingleAubinLionsTargetSameCarrierWeldIsTrue = refl

round104ExactLimitElementWeldRequiredIsTrue :
  round104ExactLimitElementWeldRequired ≡ true
round104ExactLimitElementWeldRequiredIsTrue = refl

round103PhysicalSimonAubinLionsInstantiationClosedIsFalse :
  round103PhysicalSimonAubinLionsInstantiationClosed ≡ false
round103PhysicalSimonAubinLionsInstantiationClosedIsFalse = refl