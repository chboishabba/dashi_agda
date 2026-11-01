module DASHI.Physics.Closure.NSTriadKNHHBadSimpleRationalThresholdsRound49Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Xiaoyutao Luo.
-- Title: "A Beale-Kato-Majda Criterion with Optimal Frequency and Temporal Localization".
-- DOI: 10.1007/s00021-019-0411-z.
-- arXiv DOI: 10.48550/arXiv.1803.05569.
--
-- Authors: Peter Constantin; Charles Fefferman.
-- Title: "Direction of Vorticity and the Problem of Global Regularity for the Navier-Stokes Equations".
-- DOI: 10.1512/iumj.1993.42.42034.
--
-- DASHI CONTRIBUTION
--
-- Round 49 shows that one selected coherence threshold is enough.  Before any
-- continuous optimization, expose two exact rational candidates with exact
-- inverses: delta*=1/4 and delta*=1/8.  Either can be used directly by the
-- physical recurrence target.  No assertion is made that either candidate
-- satisfies the unresolved PDE estimates.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
import Data.Integer.Base as Int
open import Data.Rational.Base using
  (ℚ; 0ℚ; 1ℚ; _/_; _*_; _≤_; _<_) 
import Data.Rational.Properties as ℚP
open ℚP using (_≤?_; _<?_)
open import Relation.Nullary.Decidable.Core using (toWitness)

import DASHI.Physics.Closure.NSTriadKNLuoBadCoherenceWeightedMarkovExact as Threshold

quarter eighth four eight : ℚ
quarter = Int.+ 1 / 4
eighth = Int.+ 1 / 8
four = Int.+ 4 / 1
eight = Int.+ 8 / 1

quarterPositive : 0ℚ < quarter
quarterPositive = toWitness {a? = 0ℚ <? quarter} _

eighthPositive : 0ℚ < eighth
eighthPositive = toWitness {a? = 0ℚ <? eighth} _

fourNonnegative : 0ℚ ≤ four
fourNonnegative = toWitness {a? = 0ℚ ≤? four} _

eightNonnegative : 0ℚ ≤ eight
eightNonnegative = toWitness {a? = 0ℚ ≤? eight} _

quarterThreshold : Threshold.PositiveThreshold
quarterThreshold = Threshold.positive-threshold
  quarter four quarterPositive fourNonnegative refl

eighthThreshold : Threshold.PositiveThreshold
eighthThreshold = Threshold.positive-threshold
  eighth eight eighthPositive eightNonnegative refl

quarterThresholdExact : Threshold.threshold quarterThreshold ≡ quarter
quarterThresholdExact = refl

eighthThresholdExact : Threshold.threshold eighthThreshold ≡ eighth
eighthThresholdExact = refl

quarterThresholdInverseExact : Threshold.thresholdInverse quarterThreshold ≡ four
quarterThresholdInverseExact = refl

eighthThresholdInverseExact : Threshold.thresholdInverse eighthThreshold ≡ eight
eighthThresholdInverseExact = refl

simpleRationalThresholdCandidatesConstructed : Bool
simpleRationalThresholdCandidatesConstructed = true

simpleRationalThresholdCandidatesConstructedIsTrue :
  simpleRationalThresholdCandidatesConstructed ≡ true
simpleRationalThresholdCandidatesConstructedIsTrue = refl
