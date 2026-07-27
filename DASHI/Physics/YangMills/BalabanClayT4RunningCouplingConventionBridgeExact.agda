module DASHI.Physics.YangMills.BalabanClayT4RunningCouplingConventionBridgeExact where

open import Agda.Builtin.Equality using (_≡_)
open import Data.Integer.Base using (+_)
open import Data.Rational using (ℚ; _*_; _/_)
open import Relation.Binary.PropositionalEquality using (cong; trans)

open import DASHI.Physics.YangMills.CompactLieProofLevel
import DASHI.Physics.YangMills.BalabanClayP3PhysicalOneStepTransferExact as P3
import DASHI.Physics.YangMills.BalabanClayT4BetaNormalizationConventionExact as Beta

------------------------------------------------------------------------
-- The running-coupling recursion is tied to one fixed convention before any
-- numerical certificate can consume it.
--
-- D. J. Gross and F. Wilczek,
-- "Ultraviolet Behavior of Non-Abelian Gauge Theories",
-- DOI: 10.1103/PhysRevLett.30.1343
--
-- H. D. Politzer,
-- "Reliable Perturbative Results for Strong Interactions?",
-- DOI: 10.1103/PhysRevLett.30.1346
--
-- R. Dashen and D. J. Gross,
-- "Relationship between lattice and continuum definitions of the gauge-theory
-- coupling",
-- DOI: 10.1103/PhysRevD.23.2340
------------------------------------------------------------------------

record ConventionMatchedRunningCoupling (Scale Scalar : Set) : Set₁ where
  field
    recursion : P3.RunningCouplingRecursion Scale Scalar

    casimirAdjoint : ℚ
    embedRational : ℚ → Scalar
    multiply : Scalar → Scalar → Scalar
    inversePiSquared : Scalar
    logBlocking : Scale → Scalar

    betaLogBlockingDefinition : ∀ scale →
      P3.betaLogBlocking recursion scale
      ≡ multiply
          (multiply
            (embedRational
              (Beta.pureYMInverseCouplingCoefficient casimirAdjoint))
            inversePiSquared)
          (logBlocking scale)

open ConventionMatchedRunningCoupling public

betaLogBlockingUsesElevenOverTwentyFour :
  ∀ {Scale Scalar}
    (dataSet : ConventionMatchedRunningCoupling Scale Scalar)
    scale →
  P3.betaLogBlocking (recursion dataSet) scale
  ≡ multiply dataSet
      (multiply dataSet
        (embedRational dataSet
          ((+ 11 / 24) * casimirAdjoint dataSet))
        (inversePiSquared dataSet))
      (logBlocking dataSet scale)
betaLogBlockingUsesElevenOverTwentyFour dataSet scale =
  trans
    (betaLogBlockingDefinition dataSet scale)
    (cong
      (λ rationalCoefficient →
        multiply dataSet
          (multiply dataSet
            (embedRational dataSet rationalCoefficient)
            (inversePiSquared dataSet))
          (logBlocking dataSet scale))
      (Beta.inverseCouplingIsElevenOverTwentyFour
        (casimirAdjoint dataSet)))

betaLogBlockingUsesBetaZeroOverEight :
  ∀ {Scale Scalar}
    (dataSet : ConventionMatchedRunningCoupling Scale Scalar)
    scale →
  P3.betaLogBlocking (recursion dataSet) scale
  ≡ multiply dataSet
      (multiply dataSet
        (embedRational dataSet
          ((+ 1 / 8) * Beta.pureYMBetaZero (casimirAdjoint dataSet)))
        (inversePiSquared dataSet))
      (logBlocking dataSet scale)
betaLogBlockingUsesBetaZeroOverEight dataSet scale =
  trans
    (betaLogBlockingDefinition dataSet scale)
    (cong
      (λ rationalCoefficient →
        multiply dataSet
          (multiply dataSet
            (embedRational dataSet rationalCoefficient)
            (inversePiSquared dataSet))
          (logBlocking dataSet scale))
      (Beta.inverseCouplingIsBetaZeroOverEight
        (casimirAdjoint dataSet)))

runningCouplingConventionBridgeLevel : ProofLevel
runningCouplingConventionBridgeLevel = machineChecked

betaNotationEquivalenceAtRecursionLevel : ProofLevel
betaNotationEquivalenceAtRecursionLevel = machineChecked

-- The literal RG producer must calculate the localized plaquette coefficient
-- and prove betaLogBlockingDefinition.  The convention bridge itself cannot
-- manufacture that coefficient from the abstract recursion.
physicalRunningCouplingCoefficientCalculationLevel : ProofLevel
physicalRunningCouplingCoefficientCalculationLevel = conditional
