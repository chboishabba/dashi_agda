module DASHI.Physics.Closure.NSTriadKNComLiftingFeasibilityRound52Exact where

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
-- If physical lifting from the scalar bandwidth-one majorant to the literal
-- shell block costs a factor m, the Young numerator becomes
--
--   (133/1024) m.
--
-- A downstream critical-coefficient cap Bcrit and a chosen soft split epsilon
-- require the division-free condition
--
--   (133/1024) m <= Bcrit epsilon.
--
-- If the reserve supplies at most epsilonMax, feasibility therefore requires
--
--   (133/1024) m <= Bcrit epsilonMax.
--
-- This is the exact rational falsification gate to evaluate BEFORE heroic work
-- removing a collision factor.  No claim is made here that any m>1 is needed.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; _*_; _≤_; nonNegative)
import Data.Rational.Properties as ℚP

import DASHI.Physics.Closure.NSTriadKNComExplicitSoftCoefficientRound50Exact as Com

liftedComYoungNumerator : ℚ → ℚ
liftedComYoungNumerator multiplicity =
  Com.oneThousandTwentyFourth133 * multiplicity

record ComLiftingAtSplit : Set where
  field
    multiplicity criticalCoefficientCap split : ℚ
    multiplicityNonnegative : 0ℚ ≤ multiplicity
    criticalCoefficientCapNonnegative : 0ℚ ≤ criticalCoefficientCap
    splitNonnegative : 0ℚ ≤ split
    liftedCoefficientFitsCap :
      liftedComYoungNumerator multiplicity
      ≤ criticalCoefficientCap * split

open ComLiftingAtSplit public

record ReserveSplitUpperBound (physical : ComLiftingAtSplit) : Set where
  field
    maximumAvailableSplit : ℚ
    maximumAvailableSplitNonnegative : 0ℚ ≤ maximumAvailableSplit
    splitBelowMaximum : split physical ≤ maximumAvailableSplit

open ReserveSplitUpperBound public

comLiftingNecessaryFeasibility :
  (physical : ComLiftingAtSplit) →
  (reserve : ReserveSplitUpperBound physical) →
  liftedComYoungNumerator (multiplicity physical)
  ≤ criticalCoefficientCap physical * maximumAvailableSplit reserve
comLiftingNecessaryFeasibility physical reserve =
  let
    capTimesSplitBelowMaximum :
      criticalCoefficientCap physical * split physical
      ≤ criticalCoefficientCap physical * maximumAvailableSplit reserve
    capTimesSplitBelowMaximum =
      let instance capNNI =
        nonNegative (criticalCoefficientCapNonnegative physical)
      in ℚP.*-monoˡ-≤-nonNeg
        (criticalCoefficientCap physical)
        (splitBelowMaximum reserve)
  in
  ℚP.≤-trans
    (liftedCoefficientFitsCap physical)
    capTimesSplitBelowMaximum

comMultiplicityMustBeTestedAgainstActualRecursionCap : Bool
comMultiplicityMustBeTestedAgainstActualRecursionCap = true

comLiftingFeasibilityGateClosed : Bool
comLiftingFeasibilityGateClosed = true

comLiftingFeasibilityGateClosedIsTrue :
  comLiftingFeasibilityGateClosed ≡ true
comLiftingFeasibilityGateClosedIsTrue = refl
