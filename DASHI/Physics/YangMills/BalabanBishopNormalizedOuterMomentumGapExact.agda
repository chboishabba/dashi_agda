module DASHI.Physics.YangMills.BalabanBishopNormalizedOuterMomentumGapExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Tadeusz Bałaban,
-- "Renormalization Group Approach to Lattice Gauge Field Theories. I.",
-- Communications in Mathematical Physics 109 (1987), 249--301.
-- DOI: 10.1007/BF01215223.
--
-- Zachary Murray,
-- "Constructive Analysis in the Agda Proof Assistant",
-- B.Sc. Honours thesis, Dalhousie University, 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Compose the normalized q -> pi |q| / 2 window with the already-proved
-- constructive outer Brillouin sine gap.  Once a literal normalized momentum
-- coordinate is known to be outer and a constructive pi enclosure
--
--     3 <= pi <= 22/7
--
-- is supplied, the entire transcendental denominator leaf reduces to the
-- existing radius-two alternating-series theorem.
------------------------------------------------------------------------

import Real as BishopReal

import DASHI.Foundations.BishopPowerSeriesElementaryBridgeExact as Elementary
import DASHI.Physics.YangMills.BalabanBishopSineTwoBallCubicLowerExact as Sine
import DASHI.Physics.YangMills.BalabanBishopOuterBrillouinSineGapExact as Gap
import DASHI.Physics.YangMills.BalabanBishopNormalizedOuterMomentumAngleExact as Angle
open import DASHI.Physics.YangMills.CompactLieProofLevel

record NormalizedOuterMomentumGapData
    (dataSet : Elementary.BishopElementaryPowerSeriesData) : Set₁ where
  field
    angleData : Angle.NormalizedOuterMomentumAngleData
    sineInputs : Sine.ConcreteTwoBallSineInputs dataSet (Angle.angle angleData)

open NormalizedOuterMomentumGapData public

normalizedOuterSineLower :
  ∀ {dataSet} →
  (data : NormalizedOuterMomentumGapData dataSet) →
  BishopReal._≤_
    (Gap.embed Gap.lowerSine)
    (Elementary.bishopSin dataSet (Angle.angle (angleData data)))
normalizedOuterSineLower data =
  Gap.sineAboveEightySevenOverOneTwentyEight
    (sineInputs data)
    (Angle.angleLower (angleData data))
    (Angle.angleUpper (angleData data))

normalizedOuterHatSquareLower :
  ∀ {dataSet} →
  (data : NormalizedOuterMomentumGapData dataSet) →
  BishopReal._≤_
    (Gap.embed Gap.hatSquareLower)
    (Gap.hatSquare dataSet (Angle.angle (angleData data)))
normalizedOuterHatSquareLower data =
  Gap.hatComponentSquareAboveFixedGap
    (sineInputs data)
    (Angle.angleLower (angleData data))
    (Angle.angleUpper (angleData data))

normalizedOuterMomentumSineGapLevel : ProofLevel
normalizedOuterMomentumSineGapLevel = machineChecked
