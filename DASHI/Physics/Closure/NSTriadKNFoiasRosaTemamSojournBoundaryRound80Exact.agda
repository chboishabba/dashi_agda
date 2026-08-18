module DASHI.Physics.Closure.NSTriadKNFoiasRosaTemamSojournBoundaryRound80Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCE / CONTEXT
--
-- Authors: Ciprian Foias; Ricardo M. S. Rosa; Roger M. Temam.
-- Title: "Convergence of time averages of weak solutions of the
-- three-dimensional Navier--Stokes equations".
-- Journal of Statistical Physics 160 (2015), 779--790.
-- DOI: 10.1007/s10955-015-1248-3.
-- arXiv: 1411.3391.
--
-- ROUND80 / C5 RESIDENCE-TIME AUTHORITY BOUNDARY
--
-- Foias--Rosa--Temam prove a rigorous recurrence/sojourn theorem without a
-- globally well-posed NS semigroup: under an invariant Vishik--Fursikov
-- measure, any positive-measure Borel set has positive mean sojourn time for
-- almost every relevant Leray--Hopf weak solution (and for almost every initial
-- condition there exists at least one such weak solution).
--
-- This is valuable infrastructure for statistical occupation questions, but it
-- does NOT directly close Round79 C5.  C5 needs a deterministic quantitative
-- UPPER bound on dangerous residence (or a lower bound on depletion accrued per
-- unit residence) for the specific selected physical trajectory.  The source
-- theorem gives an almost-everywhere/existential POSITIVITY statement.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; 0ℚ; 1ℚ; _<_; _≤_; _/_; _*_)
import Data.Integer.Base as Int

------------------------------------------------------------------------
-- Quantifier-shape countermodel.

data ToyTrajectory : Set where
  measureSupported selectedTrajectory : ToyTrajectory

regularityProperty : ToyTrajectory → Bool
regularityProperty measureSupported = true
regularityProperty selectedTrajectory = false

almostEveryToyPropertyHolds : regularityProperty measureSupported ≡ true
almostEveryToyPropertyHolds = refl

selectedToyPropertyFails : regularityProperty selectedTrajectory ≡ false
selectedToyPropertyFails = refl

record AlmostEveryImpliesSelected : Set where
  field
    promote :
      regularityProperty measureSupported ≡ true →
      regularityProperty selectedTrajectory ≡ true

open AlmostEveryImpliesSelected public

almostEveryCannotDetermineDistinguishedSelectedTrajectory :
  AlmostEveryImpliesSelected →
  false ≡ true
almostEveryCannotDetermineDistinguishedSelectedTrajectory candidate =
  promote candidate almostEveryToyPropertyHolds

------------------------------------------------------------------------
-- Sign/direction countermodel for sojourn-time information.

half : ℚ
half = Int.+ 1 / 2

record PositiveMeanSojourn : Set where
  constructor positive-mean-sojourn
  field
    sojourn : ℚ
    sojournPositive : 0ℚ < sojourn

open PositiveMeanSojourn public

unitSojourn : 0ℚ < 1ℚ → PositiveMeanSojourn
unitSojourn onePositive = positive-mean-sojourn 1ℚ onePositive

record PositiveSojournForcesHalfCap : Set where
  field
    capEveryPositiveSojourn :
      (datum : PositiveMeanSojourn) →
      sojourn datum ≤ half

open PositiveSojournForcesHalfCap public

positiveSojournCannotSupplySmallUpperResidenceCap :
  0ℚ < 1ℚ →
  PositiveSojournForcesHalfCap →
  1ℚ ≤ half
positiveSojournCannotSupplySmallUpperResidenceCap onePositive candidate =
  capEveryPositiveSojourn candidate (unitSojourn onePositive)

------------------------------------------------------------------------
-- Correct C5 consumer shapes.

record DeterministicDangerousResidenceBudget : Set where
  constructor deterministic-dangerous-residence-budget
  field
    dangerousResidence : ℚ
    residenceCap : ℚ
    dangerousResidenceNonnegative : 0ℚ ≤ dangerousResidence
    deterministicUpperBound : dangerousResidence ≤ residenceCap

open DeterministicDangerousResidenceBudget public

record DepletionPerResidenceBudget : Set where
  constructor depletion-per-residence-budget
  field
    dangerousResidence : ℚ
    depletionRate : ℚ
    availableBudget : ℚ
    residenceNonnegative : 0ℚ ≤ dangerousResidence
    depletionRateNonnegative : 0ℚ ≤ depletionRate
    fundedResidence : depletionRate * dangerousResidence ≤ availableBudget

round80FoiasRosaTemamGivesRigorousStatisticalSojourn : Bool
round80FoiasRosaTemamGivesRigorousStatisticalSojourn = true

round80StatisticalPositiveSojournClosesDeterministicC5UpperBound : Bool
round80StatisticalPositiveSojournClosesDeterministicC5UpperBound = false

round80C5StillNeedsSelectedTrajectoryResidenceOrDepletionBound : Bool
round80C5StillNeedsSelectedTrajectoryResidenceOrDepletionBound = true

round80StatisticalPositiveSojournClosesDeterministicC5UpperBoundIsFalse :
  round80StatisticalPositiveSojournClosesDeterministicC5UpperBound ≡ false
round80StatisticalPositiveSojournClosesDeterministicC5UpperBoundIsFalse = refl
