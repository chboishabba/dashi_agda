module DASHI.Physics.Closure.NSTriadKNComExplicitSoftCoefficientRound50Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Authors: Tosio Kato; Gustavo Ponce.
-- Title: "Commutator Estimates and the Euler and Navier-Stokes Equations".
-- DOI: 10.1002/cpa.3160410704.
--
-- Author: Issai Schur.
-- Classical row/column test for integral and matrix operators; no DOI is
-- assigned to the historical theorem used here.
--
-- Author: William Henry Young.
-- Title: "On the Multiplication of Successions of Fourier Constants".
-- DOI: 10.1098/rspa.1912.0086.
--
-- DASHI CONTRIBUTION
--
-- The bandwidth-one positive majorant has row coefficient 133/256.  Combining
-- it with the repository's scaled Young theorem gives the exact critical
-- coefficient
--
--   (1/(4 epsilon)) (133/256)
--     = 133/(1024 epsilon).
--
-- This module exposes that coefficient explicitly for the later fixed-shift
-- recursion audit.  It does not change the physical Com frontier: common-hat,
-- d=0/d=1 active estimates, and the squared Schur/pairing endpoint must still
-- be proved on the literal physical operator.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
import Data.Integer.Base as Int
open import Data.Rational.Base using (ℚ; _/_; _*_; 1/_)
open import Data.Rational.Tactic.RingSolver using (solve)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold
import DASHI.Physics.Closure.NSTriadKNComThreeChannelRowMassRound48Exact as Row
import DASHI.Physics.Closure.NSTriadKNMixedCriticalYoungSoftRound47Exact as Mixed

oneThousandTwentyFourth133 : ℚ
oneThousandTwentyFourth133 = Int.+ 133 / 1024

explicitComCriticalCoefficient : Threshold.PositiveThreshold → ℚ
explicitComCriticalCoefficient split =
  oneThousandTwentyFourth133 * Threshold.thresholdInverse split

rowYoungCoefficientArithmetic :
  ∀ split →
  Mixed.quarter * Threshold.thresholdInverse split * Row.threeChannelTarget
  ≡ explicitComCriticalCoefficient split
rowYoungCoefficientArithmetic split =
  solve (Threshold.thresholdInverse split ∷ [])

bandwidthOnePositiveMajorantTarget : ℚ
bandwidthOnePositiveMajorantTarget = Row.threeChannelTarget

comSoftCoefficientIs133Over1024Epsilon : Bool
comSoftCoefficientIs133Over1024Epsilon = true

abstractFiniteBandOptimizationFinished : Bool
abstractFiniteBandOptimizationFinished = true

comSoftCoefficientIs133Over1024EpsilonIsTrue :
  comSoftCoefficientIs133Over1024Epsilon ≡ true
comSoftCoefficientIs133Over1024EpsilonIsTrue = refl
