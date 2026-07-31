module DASHI.Physics.YangMills.BalabanClayGate4DyadicRunningCouplingConventionExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
import Data.Rational.Tactic.RingSolver as ℚRing
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel

import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta
import DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact as Running
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3

------------------------------------------------------------------------
-- Primary provenance.
--
-- David J. Gross and Frank Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- Physical Review Letters 30 (1973), 1343--1346.
-- DOI: 10.1103/PhysRevLett.30.1343.
--
-- H. David Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- Physical Review Letters 30 (1973), 1346--1349.
-- DOI: 10.1103/PhysRevLett.30.1346.
--
-- Roger Dashen and David J. Gross,
-- "Relationship between Lattice and Continuum Definitions of the Gauge-Theory
-- Coupling", Physical Review D 23 (1981), 2340--2348.
-- DOI: 10.1103/PhysRevD.23.2340.
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.
-- Generation of Effective Actions in a Small Field Approximation and a
-- Coupling Constant Renormalization in Four Dimensions",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Locator-only comparison:
-- Lluis Eriksson, "Uniform Poincare Inequality for Lattice Yang-Mills Theory
-- Via Multiscale Martingale Decomposition", ai.viXra:2602.0040, no DOI.
-- The locator writes beta_k = beta + 2 b0 k log 2 + O(1/beta), with
-- b0 = 11 C_A/(48 pi^2). The rational reconciliation below is exact; the
-- remainder estimate and identification with Bałaban's localized coefficient
-- are not imported from that document.
------------------------------------------------------------------------

locatorB0Rational : ℚ → ℚ
locatorB0Rational casimirAdjoint = (+ 11 / 48) * casimirAdjoint

locatorTwiceB0EqualsInverseCouplingCoefficient : ∀ casimirAdjoint →
  (+ 2 / 1) * locatorB0Rational casimirAdjoint
  ≡ Beta.pureYMInverseCouplingCoefficient casimirAdjoint
locatorTwiceB0EqualsInverseCouplingCoefficient casimirAdjoint =
  ℚRing.solve-∀ casimirAdjoint

elevenOverTwentyFourEqualsTwiceLocatorB0 : ∀ casimirAdjoint →
  (+ 11 / 24) * casimirAdjoint
  ≡ (+ 2 / 1) * locatorB0Rational casimirAdjoint
elevenOverTwentyFourEqualsTwiceLocatorB0 casimirAdjoint =
  trans
    (sym (Beta.inverseCouplingIsElevenOverTwentyFour casimirAdjoint))
    (sym (locatorTwiceB0EqualsInverseCouplingCoefficient casimirAdjoint))

record DyadicRunningCouplingConvention (Scale Scalar : Set) : Set₁ where
  field
    running : Running.ConventionMatchedRunningCoupling Scale Scalar

    dyadicLog : Scalar
    scaleIsDyadic : ∀ scale →
      Running.logBlocking running scale ≡ dyadicLog

open DyadicRunningCouplingConvention public

dyadicIncrementUsesTwiceLocatorB0 :
  ∀ {Scale Scalar}
    (dataSet : DyadicRunningCouplingConvention Scale Scalar)
    scale →
  P3.betaLogBlocking (Running.recursion (running dataSet)) scale
  ≡ Running.multiply (running dataSet)
      (Running.multiply (running dataSet)
        (Running.embedRational (running dataSet)
          ((+ 2 / 1) * locatorB0Rational
            (Running.casimirAdjoint (running dataSet))))
        (Running.inversePiSquared (running dataSet)))
      (dyadicLog dataSet)
dyadicIncrementUsesTwiceLocatorB0 dataSet scale =
  trans
    (Running.betaLogBlockingUsesElevenOverTwentyFour
      (running dataSet) scale)
    (trans
      (cong
        (λ logValue →
          Running.multiply (running dataSet)
            (Running.multiply (running dataSet)
              (Running.embedRational (running dataSet)
                ((+ 11 / 24) *
                  Running.casimirAdjoint (running dataSet)))
              (Running.inversePiSquared (running dataSet)))
            logValue)
        (scaleIsDyadic dataSet scale))
      (cong
        (λ rationalCoefficient →
          Running.multiply (running dataSet)
            (Running.multiply (running dataSet)
              (Running.embedRational (running dataSet) rationalCoefficient)
              (Running.inversePiSquared (running dataSet)))
            (dyadicLog dataSet))
        (elevenOverTwentyFourEqualsTwiceLocatorB0
          (Running.casimirAdjoint (running dataSet)))))

record HRBetaRemainderControl
    {Scale Scalar : Set}
    (dataSet : DyadicRunningCouplingConvention Scale Scalar) : Set₁ where
  field
    beta inverseCouplingRemainder : Scale → Scalar
    add : Scalar → Scalar → Scalar
    absolute halfOf : Scalar → Scalar
    LessEqual : Scalar → Scalar → Set
    previous : Scale → Scale

    exactOneStepRecursion : ∀ scale →
      beta scale
      ≡ add (beta (previous scale))
          (add
            (P3.betaLogBlocking
              (Running.recursion (running dataSet)) scale)
            (inverseCouplingRemainder scale))

    remainderBelowHalfDyadicIncrement : ∀ scale →
      LessEqual (absolute (inverseCouplingRemainder scale))
        (halfOf
          (P3.betaLogBlocking
            (Running.recursion (running dataSet)) scale))

open HRBetaRemainderControl public

locatorB0ConventionReconciliationLevel : ProofLevel
locatorB0ConventionReconciliationLevel = machineChecked

dyadicIncrementConventionLevel : ProofLevel
dyadicIncrementConventionLevel = machineChecked

physicalLocalizedPlaquetteCoefficientInputsLevel : ProofLevel
physicalLocalizedPlaquetteCoefficientInputsLevel = conditional

physicalHRBetaRemainderInputsLevel : ProofLevel
physicalHRBetaRemainderInputsLevel = conditional

-- The locator is inadmissible as theorem authority.  ProofLevel has no
-- quarantine constructor; the open locator claim is therefore conjectural.
locatorRunningCouplingFormulaAcceptedAsAuthority : ProofLevel
locatorRunningCouplingFormulaAcceptedAsAuthority = conjectural
