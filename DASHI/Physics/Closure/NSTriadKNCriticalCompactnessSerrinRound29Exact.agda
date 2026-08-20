module DASHI.Physics.Closure.NSTriadKNCriticalCompactnessSerrinRound29Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: James Serrin.
-- Title: "On the Interior Regularity of Weak Solutions of the Navier-Stokes
-- Equations".
-- DOI: 10.1007/BF02392477.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- Author: Jacques Simon.
-- Title: "Compact Sets in the Space L^p(0,T;B)".
-- Annali di Matematica Pura ed Applicata 146 (1987), 65--96.
-- DOI: 10.1007/BF01762360.
--
-- DASHI CONTRIBUTION
--
-- Name the missing time-regularity input for Galerkin compactness and prove the
-- exact quantitative critical-to-Serrin budget algebra. The physical negative
-- Sobolev estimate, Aubin-Lions-Simon compactness and periodic Serrin
-- continuation remain separate producers.
--
-- ROUND104 RECEIPT REPAIR
--
-- The original abstract Aubin--Lions target stored proposition *types* as Set
-- fields without requiring inhabitants.  The target now pairs every named
-- analytic proposition with an explicit witness.  This is still an abstract
-- interface rather than a literal Sobolev-function-space construction; the
-- physical instantiation status therefore remains false.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; _/_; _+_; _*_; _≤_; NonNegative; nonNegative)
import Data.Rational.Properties as ℚₚ
open import Data.Rational.Tactic.RingSolver using (solve)

record NegativeNormTimeDerivativeBudget : Set where
  constructor negative-norm-time-derivative-budget
  field
    derivativeNorm viscousNorm nonlinearNorm : ℚ
    derivativeSplitBound : derivativeNorm ≤ viscousNorm + nonlinearNorm
    viscousBudget nonlinearBudget : ℚ
    viscousBound : viscousNorm ≤ viscousBudget
    nonlinearBound : nonlinearNorm ≤ nonlinearBudget

open NegativeNormTimeDerivativeBudget public

timeDerivativeBoundFromEquation :
  (budget : NegativeNormTimeDerivativeBudget) →
  derivativeNorm budget ≤ viscousBudget budget + nonlinearBudget budget
timeDerivativeBoundFromEquation budget =
  ℚₚ.≤-trans
    (derivativeSplitBound budget)
    (ℚₚ.+-mono-≤ (viscousBound budget) (nonlinearBound budget))

record CriticalToSerrinBudget : Set where
  constructor critical-to-serrin-budget
  field
    supHOneHalfSquared : ℚ
    integralHThreeHalfSquared : ℚ
    integralHOneFourth : ℚ
    integralL6Fourth : ℚ
    sobolevConstantFourth : ℚ

    sobolevConstantNonnegative : 0ℚ ≤ sobolevConstantFourth

    interpolationFourth :
      integralHOneFourth
      ≤ supHOneHalfSquared * integralHThreeHalfSquared

    periodicSobolevFourth :
      integralL6Fourth
      ≤ sobolevConstantFourth * integralHOneFourth

open CriticalToSerrinBudget public

criticalToSerrinQuantitative :
  (budget : CriticalToSerrinBudget) →
  integralL6Fourth budget
  ≤ sobolevConstantFourth budget
    * (supHOneHalfSquared budget * integralHThreeHalfSquared budget)
criticalToSerrinQuantitative budget =
  ℚₚ.≤-trans
    (periodicSobolevFourth budget)
    (ℚₚ.*-monoˡ-≤-nonNeg
      (sobolevConstantFourth budget)
      (interpolationFourth budget))
  where
  instance
    sobolevNN : NonNegative (sobolevConstantFourth budget)
    sobolevNN = nonNegative (sobolevConstantNonnegative budget)

serrinExponentIdentity :
  (Int.+ 2 / 4) + (Int.+ 3 / 6) ≡ Int.+ 1 / 1
serrinExponentIdentity = solve []

record CriticalAubinLionsTarget : Set₁ where
  field
    GalerkinSequence : Set
    LimitState : Set

    uniformLInfinityHOneHalf : Set
    uniformLInfinityHOneHalfWitness : uniformLInfinityHOneHalf

    uniformL2HThreeHalf : Set
    uniformL2HThreeHalfWitness : uniformL2HThreeHalf

    uniformTimeDerivativeNegativeHalf : Set
    uniformTimeDerivativeNegativeHalfWitness : uniformTimeDerivativeNegativeHalf

    strongL2HOneHalfCompactness : Set
    strongL2HOneHalfCompactnessWitness : strongL2HOneHalfCompactness

    quadraticTermConvergence : Set
    quadraticTermConvergenceWitness : quadraticTermConvergence

    initialTraceRecovered : Set
    initialTraceRecoveredWitness : initialTraceRecovered

open CriticalAubinLionsTarget public

record PeriodicSerrinContinuationTarget : Set₁ where
  field
    StrongSolution : Set
    L4L6Finite : StrongSolution → Set
    ExtendsPastMaximalTime : StrongSolution → Set
    serrinContinuation :
      (solution : StrongSolution) →
      L4L6Finite solution → ExtendsPastMaximalTime solution

open PeriodicSerrinContinuationTarget public

criticalToSerrinQuantitativeReducerClosed : Bool
criticalToSerrinQuantitativeReducerClosed = true

round104CriticalAubinLionsTargetRequiresWitnesses : Bool
round104CriticalAubinLionsTargetRequiresWitnesses = true

physicalNegativeNormTimeDerivativeClosed : Bool
physicalNegativeNormTimeDerivativeClosed = false

criticalAubinLionsInstantiated : Bool
criticalAubinLionsInstantiated = false

periodicSerrinContinuationInstantiated : Bool
periodicSerrinContinuationInstantiated = false

criticalToSerrinQuantitativeReducerClosedIsTrue :
  criticalToSerrinQuantitativeReducerClosed ≡ true
criticalToSerrinQuantitativeReducerClosedIsTrue = refl

round104CriticalAubinLionsTargetRequiresWitnessesIsTrue :
  round104CriticalAubinLionsTargetRequiresWitnesses ≡ true
round104CriticalAubinLionsTargetRequiresWitnessesIsTrue = refl

physicalNegativeNormTimeDerivativeClosedIsFalse :
  physicalNegativeNormTimeDerivativeClosed ≡ false
physicalNegativeNormTimeDerivativeClosedIsFalse = refl