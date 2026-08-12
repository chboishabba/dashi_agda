module DASHI.Physics.Closure.NSTriadKNComGlobalSoftCompatibilityRound51Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- DASHI CONTRIBUTION
--
-- `YoungSoft` means no positive eta floor is forced by the LOCAL owner theorem.
-- The later fixed-shift/block recursion can still cap the accompanying critical
-- coefficient.  For Com the exact Round-50 coefficient is
--
--   c_Com / epsilon,   c_Com = 133/1024.
--
-- If a downstream consumer requires this coefficient <= Bcrit, positivity of
-- epsilon implies the division-free minimum-split condition
--
--   c_Com <= Bcrit * epsilon.
--
-- Round 51 DERIVES that condition from the coefficient cap; it is not another
-- field supplied by the caller.  Thus global continuation compatibility can
-- force a positive minimum soft split even while the local owner hard floor is
-- zero.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; subst; trans)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNComExplicitSoftCoefficientRound50Exact as Com

record GlobalComRecursionCompatibility
    (split : Threshold.PositiveThreshold) : Set where
  field
    criticalCoefficientCap : ℚ
    criticalCoefficientCapNonnegative : 0ℚ ≤ criticalCoefficientCap

    explicitCoefficientFitsCap :
      Com.explicitComCriticalCoefficient split ≤ criticalCoefficientCap

open GlobalComRecursionCompatibility public

explicitCoefficientTimesSplitIsNumerator :
  (split : Threshold.PositiveThreshold) →
  Com.explicitComCriticalCoefficient split * Threshold.threshold split
  ≡ Com.oneThousandTwentyFourth133
explicitCoefficientTimesSplitIsNumerator split =
  let
    regroup :
      (Com.oneThousandTwentyFourth133 * Threshold.thresholdInverse split)
        * Threshold.threshold split
      ≡ Com.oneThousandTwentyFourth133
        * (Threshold.thresholdInverse split * Threshold.threshold split)
    regroup = solve
      ( Com.oneThousandTwentyFourth133
      ∷ Threshold.thresholdInverse split
      ∷ Threshold.threshold split
      ∷ [])

    cancel :
      Com.oneThousandTwentyFourth133
        * (Threshold.thresholdInverse split * Threshold.threshold split)
      ≡ Com.oneThousandTwentyFourth133 * 1ℚ
    cancel =
      cong (Com.oneThousandTwentyFourth133 *_)
        (Threshold.inverseMeaning split)

    finish :
      Com.oneThousandTwentyFourth133 * 1ℚ
      ≡ Com.oneThousandTwentyFourth133
    finish = ℚP.*-identityʳ Com.oneThousandTwentyFourth133
  in trans regroup (trans cancel finish)

clearedMinimumSplitCondition :
  ∀ {split} →
  GlobalComRecursionCompatibility split →
  Com.oneThousandTwentyFourth133
  ≤ criticalCoefficientCap _ * Threshold.threshold split
clearedMinimumSplitCondition {split} compatible =
  let
    scaled :
      Com.explicitComCriticalCoefficient split * Threshold.threshold split
      ≤ criticalCoefficientCap compatible * Threshold.threshold split
    scaled =
      let instance splitNNI =
        nonNegative (Threshold.thresholdNonnegative split)
      in ℚP.*-monoʳ-≤-nonNeg
        (Threshold.threshold split)
        (explicitCoefficientFitsCap compatible)
  in
  subst
    (λ left → left
      ≤ criticalCoefficientCap compatible * Threshold.threshold split)
    (explicitCoefficientTimesSplitIsNumerator split)
    scaled

record ComGlobalSoftSplitRequirement : Set where
  field
    minimumSplit : ℚ
    minimumSplitNonnegative : 0ℚ ≤ minimumSplit
    everyGloballyCompatibleSplitAboveMinimum :
      ∀ split →
      GlobalComRecursionCompatibility split →
      minimumSplit ≤ Threshold.threshold split

open ComGlobalSoftSplitRequirement public

localComHardFloor : ℚ
localComHardFloor = 0ℚ

localYoungSoftDoesNotProveGlobalArbitrarilySmallSplit : Bool
localYoungSoftDoesNotProveGlobalArbitrarilySmallSplit = true

globalComMinimumMustBeAuditedAtBlockRecursion : Bool
globalComMinimumMustBeAuditedAtBlockRecursion = true

localYoungSoftDoesNotProveGlobalArbitrarilySmallSplitIsTrue :
  localYoungSoftDoesNotProveGlobalArbitrarilySmallSplit ≡ true
localYoungSoftDoesNotProveGlobalArbitrarilySmallSplitIsTrue = refl

globalComMinimumMustBeAuditedAtBlockRecursionIsTrue :
  globalComMinimumMustBeAuditedAtBlockRecursion ≡ true
globalComMinimumMustBeAuditedAtBlockRecursionIsTrue = refl
