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
-- epsilon rewrites the compatibility condition without division as
--
--   c_Com <= Bcrit * epsilon.
--
-- Thus a global continuation theorem may impose a minimum admissible soft split
-- even though the local owner floor is zero.  This module records that seam
-- explicitly so the final reserve audit cannot confuse local softness with
-- globally arbitrary epsilon.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNComExplicitSoftCoefficientRound50Exact as Com

record GlobalComRecursionCompatibility
    (split : Threshold.PositiveThreshold) : Set where
  field
    criticalCoefficientCap : ℚ
    criticalCoefficientCapNonnegative : 0ℚ ≤ criticalCoefficientCap

    explicitCoefficientFitsCap :
      Com.explicitComCriticalCoefficient split ≤ criticalCoefficientCap

    clearedMinimumSplitCondition :
      Com.oneThousandTwentyFourth133
      ≤ criticalCoefficientCap * Threshold.threshold split

open GlobalComRecursionCompatibility public

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
