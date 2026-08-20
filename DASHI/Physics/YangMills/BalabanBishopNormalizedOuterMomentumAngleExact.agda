module DASHI.Physics.YangMills.BalabanBishopNormalizedOuterMomentumAngleExact where

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
-- Close the algebraic part of the normalized Brillouin-coordinate bridge.
-- For an outer normalized coordinate q with
--
--     1/2 <= |q| <= 1
--
-- and any constructive-real pi satisfying
--
--     3 <= pi <= 22/7,
--
-- the literal half-angle
--
--     t = pi |q| / 2
--
-- lies in
--
--     3/4 <= t <= 11/7.
--
-- This is exactly the hypothesis consumed by
-- BalabanBishopOuterBrillouinSineGapExact, which then gives
-- sin(t) >= 87/128 and (2 sin t)^2 >= 7569/4096.
-- No transcendental estimate is hidden here: only ordered-real multiplication
-- and the source-facing enclosure 3 <= pi <= 22/7 remain.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using (ℚᵘ; _/_)

import Real as BishopReal
import RealProperties as BishopProperties

import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

half one three twentyTwoSevenths threeQuarters elevenSevenths : ℚᵘ
half = + 1 / 2
one = + 1 / 1
three = + 3 / 1
twentyTwoSevenths = + 22 / 7
threeQuarters = + 3 / 4
elevenSevenths = + 11 / 7

embed : ℚᵘ → BishopReal.ℝ
embed = BishopReal._⋆

halfNN : BishopReal.NonNegative (embed half)
halfNN = Order.embeddedRationalNonnegative half nonNeg

oneNN : BishopReal.NonNegative (embed one)
oneNN = Order.embeddedRationalNonnegative one nonNeg

threeNN : BishopReal.NonNegative (embed three)
threeNN = Order.embeddedRationalNonnegative three nonNeg

record NormalizedOuterMomentumAngleData : Set₁ where
  field
    piValue qAbs angle : BishopReal.ℝ

    piNonnegative : BishopReal.NonNegative piValue
    qAbsNonnegative : BishopReal.NonNegative qAbs

    piLower : BishopReal._≤_ (embed three) piValue
    piUpper : BishopReal._≤_ piValue (embed twentyTwoSevenths)

    qOuterLower : BishopReal._≤_ (embed half) qAbs
    qOuterUpper : BishopReal._≤_ qAbs (embed one)

    angleDefinition :
      BishopReal._≃_ angle
        (BishopReal._*_
          (embed half)
          (BishopReal._*_ piValue qAbs))

open NormalizedOuterMomentumAngleData public

lowerProduct :
  (data : NormalizedOuterMomentumAngleData) →
  BishopReal._≤_
    (BishopReal._*_ (embed three) (embed half))
    (BishopReal._*_ (piValue data) (qAbs data))
lowerProduct data =
  BishopProperties.*-mono-≤
    threeNN halfNN
    (piLower data)
    (qOuterLower data)

upperPiNN : BishopReal.NonNegative (embed twentyTwoSevenths)
upperPiNN = Order.embeddedRationalNonnegative twentyTwoSevenths nonNeg

upperProduct :
  (data : NormalizedOuterMomentumAngleData) →
  BishopReal._≤_
    (BishopReal._*_ (piValue data) (qAbs data))
    (BishopReal._*_ (embed twentyTwoSevenths) (embed one))
upperProduct data =
  BishopProperties.*-mono-≤
    (piNonnegative data) (qAbsNonnegative data)
    (piUpper data) (qOuterUpper data)

halfTimesThreeHalfIdentity :
  BishopReal._≃_
    (BishopReal._*_
      (embed half)
      (BishopReal._*_ (embed three) (embed half)))
    (embed threeQuarters)
halfTimesThreeHalfIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ half ⊗ (Κ three ⊗ Κ half) ⊜ Κ threeQuarters)
      BishopProperties.≃-refl

halfTimesTwentyTwoSeventhsIdentity :
  BishopReal._≃_
    (BishopReal._*_
      (embed half)
      (BishopReal._*_ (embed twentyTwoSevenths) (embed one)))
    (embed elevenSevenths)
halfTimesTwentyTwoSeventhsIdentity =
  let open BishopProperties.ℝ-Solver
  in solve 0
      (Κ half ⊗ (Κ twentyTwoSevenths ⊗ Κ one) ⊜ Κ elevenSevenths)
      BishopProperties.≃-refl

angleLower :
  (data : NormalizedOuterMomentumAngleData) →
  BishopReal._≤_ (embed threeQuarters) (angle data)
angleLower data =
  let
    scaled = BishopProperties.*-monoˡ-≤-nonNeg
      (lowerProduct data) halfNN
    source : BishopReal._≤_
      (BishopReal._*_
        (embed half)
        (BishopReal._*_ (embed three) (embed half)))
      (BishopReal._*_
        (embed half)
        (BishopReal._*_ (piValue data) (qAbs data)))
    source = scaled
  in
  BishopProperties.≤-respˡ-≃
    halfTimesThreeHalfIdentity
    (BishopProperties.≤-respʳ-≃
      (BishopProperties.≃-symm (angleDefinition data))
      source)

angleUpper :
  (data : NormalizedOuterMomentumAngleData) →
  BishopReal._≤_ (angle data) (embed elevenSevenths)
angleUpper data =
  let
    scaled = BishopProperties.*-monoˡ-≤-nonNeg
      (upperProduct data) halfNN
  in
  BishopProperties.≤-respˡ-≃
    (angleDefinition data)
    (BishopProperties.≤-respʳ-≃
      halfTimesTwentyTwoSeventhsIdentity
      scaled)

normalizedOuterMomentumAngleWindowLevel : ProofLevel
normalizedOuterMomentumAngleWindowLevel = machineChecked

constructivePiThreeToTwentyTwoSeventhsInputLevel : ProofLevel
constructivePiThreeToTwentyTwoSeventhsInputLevel = conditional
