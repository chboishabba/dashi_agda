module DASHI.Foundations.BishopMachinPiRationalWindowExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- John Machin (1706), classical identity
--     pi/4 = 4 atan(1/5) - atan(1/239).
-- Historical source; no DOI.
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
-- Prove a completely rational window for the ACTUAL convergent Bishop Machin
-- real.  We deliberately use coarse bounds with generous slack:
--
--   atan(1/5) >= 1/5 - (1/5)^3/3,
--   atan(1/239) <= 1/239,
--
-- giving the lower certificate
--
--   16*(74/375) - 4/239 = 3 + 12601/89625 > 3.
--
-- For the upper side we use
--
--   atan(1/5) <= 1/5 - (1/5)^3/3 + (1/5)^5/5,
--   atan(1/239) >= 1/240,
--
-- where the latter follows from the cubic lower bracket with positive margin
-- 57041/3276460560.  Hence
--
--   pi_M <= 16*(9253/46875) - 4/240
--        = 22/7 - 1531/1312500 < 22/7.
--
-- No decimal approximation, global trigonometric identity or pi oracle enters
-- the proof.
------------------------------------------------------------------------

open import Data.Integer.Base using (+_; nonNeg)
open import Data.Rational.Unnormalised as ℚ using
  (ℚᵘ; 0ℚᵘ; _/_; _+_; _-_; _<_; _≤_)
import Data.Rational.Unnormalised.Properties as ℚP

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Foundations.BishopArctanHalfBallInterlacingExact as Interlace
import DASHI.Foundations.BishopArctanCubicQuinticPolynomialExact as Poly
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Limits
import DASHI.Physics.YangMills.BalabanP33BishopLowOrderTaylorBracketsExact as Low
import DASHI.Physics.YangMills.BalabanP33BishopInverseDexpCoefficientExact as Order
open import DASHI.Physics.YangMills.CompactLieProofLevel

three twentyTwoSevenths oneTwoFortieth : ℚᵘ
three = + 3 / 1
twentyTwoSevenths = + 22 / 7
oneTwoFortieth = + 1 / 240

lowerMargin upperMargin bCubicMargin : ℚᵘ
lowerMargin = + 12601 / 89625
upperMargin = + 1531 / 1312500
bCubicMargin = + 57041 / 3276460560

lowerRational upperRational : ℚᵘ
lowerRational = three ℚ.+ lowerMargin
upperRational = twentyTwoSevenths ℚ.- upperMargin

embed : ℚᵘ → Bishop.ℝ
embed = Bishop._⋆

oneFifthPoint : Interlace.PositiveHalfBallPoint Atan.bishopOneFifth
oneFifthPoint =
  Interlace.positiveHalfBallPoint
    Atan.oneFifthNonnegative
    Atan.bishopOneFifthInsideHalf

oneTwoHundredThirtyNinthPoint :
  Interlace.PositiveHalfBallPoint Atan.bishopOneTwoHundredThirtyNinth
oneTwoHundredThirtyNinthPoint =
  Interlace.positiveHalfBallPoint
    Atan.oneTwoHundredThirtyNinthNonnegative
    Atan.bishopOneTwoHundredThirtyNinthInsideHalf

sixteenNN : Bishop.NonNegative (embed Atan.sixteen)
sixteenNN = Order.embeddedRationalNonnegative Atan.sixteen nonNeg

fourNN : Bishop.NonNegative (embed Atan.four)
fourNN = Order.embeddedRationalNonnegative Atan.four nonNeg

atanUpperByValue : ∀ {value} →
  (point : Interlace.PositiveHalfBallPoint value) →
  Bishop._≤_
    (Atan.bishopAtanHalfBall value (Interlace.insideHalf point))
    value
atanUpperByValue {value} point =
  let
    dataSet = Interlace.atanAlternatingSeriesData point
    raw = Limits.representedLimitBelowUpperPartial
      (Interlace.atanInterlacing point) 0
    upperIsMagnitude = Low.upperZeroEquivalentFirstMagnitude dataSet
    magnitudeIsValue = Poly.magnitudeZeroIsValue (Interlace.nonnegative point)
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-trans upperIsMagnitude magnitudeIsValue)
    raw

oneTwoFortiethBelowCubicB :
  Bishop._≤_ (embed oneTwoFortieth)
    (Poly.atanCubic Atan.bishopOneTwoHundredThirtyNinth)
oneTwoFortiethBelowCubicB =
  let
    marginNN = Order.embeddedRationalNonnegative bCubicMargin nonNeg
    basePlusMargin :
      Bishop._≤_ (embed oneTwoFortieth)
        (Bishop._+_ (embed oneTwoFortieth) (embed bCubicMargin))
    basePlusMargin =
      BishopP.≤-respˡ-≃
        (BishopP.≃-symm (BishopP.+-identityʳ (embed oneTwoFortieth)))
        (BishopP.+-monoʳ-≤ (embed oneTwoFortieth)
          (BishopP.nonNegx⇒0≤x marginNN))
    cubicAsBasePlusMargin :
      Bishop._≃_
        (Poly.atanCubic Atan.bishopOneTwoHundredThirtyNinth)
        (Bishop._+_ (embed oneTwoFortieth) (embed bCubicMargin))
    cubicAsBasePlusMargin =
      let open BishopP.ℝ-Solver
      in solve 0
        (Κ (+ 1 / 239)
          ⊖ (Κ (+ 1 / 3) ⊗ ((Κ (+ 1 / 239) ⊗ Κ (+ 1 / 239)) ⊗ Κ (+ 1 / 239)))
          ⊜ Κ (+ 1 / 240) ⊕ Κ (+ 57041 / 3276460560))
        BishopP.≃-refl
  in
  BishopP.≤-respʳ-≃
    (BishopP.≃-symm cubicAsBasePlusMargin)
    basePlusMargin

oneTwoFortiethBelowAtanB :
  Bishop._≤_ (embed oneTwoFortieth) Atan.bishopAtanOneTwoHundredThirtyNinth
oneTwoFortiethBelowAtanB =
  BishopP.≤-trans
    oneTwoFortiethBelowCubicB
    (Poly.atanCubicLower oneTwoHundredThirtyNinthPoint)

machinLowerCandidate machinUpperCandidate : Bishop.ℝ
machinLowerCandidate =
  Bishop._-_
    (Bishop._*_ (embed Atan.sixteen) (Poly.atanCubic Atan.bishopOneFifth))
    (Bishop._*_ (embed Atan.four) Atan.bishopOneTwoHundredThirtyNinth)

machinUpperCandidate =
  Bishop._-_
    (Bishop._*_ (embed Atan.sixteen) (Poly.atanQuintic Atan.bishopOneFifth))
    (Bishop._*_ (embed Atan.four) (embed oneTwoFortieth))

machinLowerCandidateSound :
  Bishop._≤_ machinLowerCandidate Atan.bishopMachinPi
machinLowerCandidateSound =
  let
    scaledA = BishopP.*-monoˡ-≤-nonNeg
      (Poly.atanCubicLower oneFifthPoint) sixteenNN
    scaledB = BishopP.*-monoˡ-≤-nonNeg
      (atanUpperByValue oneTwoHundredThirtyNinthPoint) fourNN
    negScaledB = BishopP.neg-mono-≤ scaledB
  in
  BishopP.+-mono-≤ scaledA negScaledB

machinUpperCandidateSound :
  Bishop._≤_ Atan.bishopMachinPi machinUpperCandidate
machinUpperCandidateSound =
  let
    scaledA = BishopP.*-monoˡ-≤-nonNeg
      (Poly.atanQuinticUpper oneFifthPoint) sixteenNN
    scaledB = BishopP.*-monoˡ-≤-nonNeg oneTwoFortiethBelowAtanB fourNN
    negScaledB = BishopP.neg-mono-≤ scaledB
  in
  BishopP.+-mono-≤ scaledA negScaledB

machinLowerCandidateIsRational :
  Bishop._≃_ machinLowerCandidate (embed lowerRational)
machinLowerCandidateIsRational =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ (+ 16 / 1) ⊗
       (Κ (+ 1 / 5) ⊖
        (Κ (+ 1 / 3) ⊗ ((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5)))))
      ⊖ (Κ (+ 4 / 1) ⊗ Κ (+ 1 / 239))
      ⊜ Κ lowerRational)
    BishopP.≃-refl

machinUpperCandidateIsRational :
  Bishop._≃_ machinUpperCandidate (embed upperRational)
machinUpperCandidateIsRational =
  let open BishopP.ℝ-Solver
  in solve 0
    ((Κ (+ 16 / 1) ⊗
       ((Κ (+ 1 / 5) ⊖
         (Κ (+ 1 / 3) ⊗ ((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5))))
        ⊕
        (Κ (+ 1 / 5) ⊗
          (((Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5)) ⊗ Κ (+ 1 / 5))
            ⊗ (Κ (+ 1 / 5) ⊗ Κ (+ 1 / 5))))))
      ⊖ (Κ (+ 4 / 1) ⊗ Κ (+ 1 / 240))
      ⊜ Κ upperRational)
    BishopP.≃-refl

threeBelowLowerRational : three ℚ.< lowerRational
threeBelowLowerRational =
  ℚP.<-respˡ-≃
    (ℚP.≃-sym (ℚP.+-identityʳ three))
    (ℚP.+-monoʳ-< three (ℚP.positive⁻¹ lowerMargin))

upperRationalBelowTwentyTwoSevenths :
  upperRational ℚ.< twentyTwoSevenths
upperRationalBelowTwentyTwoSevenths =
  let
    zeroBelowMargin : 0ℚᵘ ℚ.< upperMargin
    zeroBelowMargin = ℚP.positive⁻¹ upperMargin
    raw :
      twentyTwoSevenths ℚ.- upperMargin
      ℚ.< twentyTwoSevenths ℚ.- 0ℚᵘ
    raw = ℚP.+-monoʳ-< twentyTwoSevenths
      (ℚP.neg-mono-< zeroBelowMargin)
  in
  ℚP.<-respʳ-≃
    (ℚP.+-identityʳ twentyTwoSevenths)
    raw

threeBelowMachinPi : Bishop._<_ (embed three) Atan.bishopMachinPi
threeBelowMachinPi =
  BishopP.<-≤-trans
    (BishopP.<-respʳ-≃
      (BishopP.≃-symm machinLowerCandidateIsRational)
      (BishopP.p<q⇒p⋆<q⋆ three lowerRational threeBelowLowerRational))
    machinLowerCandidateSound

machinPiBelowTwentyTwoSevenths :
  Bishop._<_ Atan.bishopMachinPi (embed twentyTwoSevenths)
machinPiBelowTwentyTwoSevenths =
  BishopP.≤-<-trans
    machinUpperCandidateSound
    (BishopP.<-respˡ-≃
      machinUpperCandidateIsRational
      (BishopP.p<q⇒p⋆<q⋆
        upperRational twentyTwoSevenths
        upperRationalBelowTwentyTwoSevenths))

threeBelowMachinPiNonStrict : Bishop._≤_ (embed three) Atan.bishopMachinPi
threeBelowMachinPiNonStrict = BishopP.<⇒≤ threeBelowMachinPi

machinPiBelowTwentyTwoSeventhsNonStrict :
  Bishop._≤_ Atan.bishopMachinPi (embed twentyTwoSevenths)
machinPiBelowTwentyTwoSeventhsNonStrict =
  BishopP.<⇒≤ machinPiBelowTwentyTwoSevenths

bishopMachinPiThreeToTwentyTwoSeventhsLevel : ProofLevel
bishopMachinPiThreeToTwentyTwoSeventhsLevel = machineChecked

-- This closes the NUMERICAL pi window required by normalized momentum.
-- The remaining pi issue is only semantic: identify `bishopMachinPi` with the
-- same trigonometric/Fourier period used by the Wilson momentum convention.
bishopMachinPiTrigPeriodIdentificationLevel : ProofLevel
bishopMachinPiTrigPeriodIdentificationLevel = conditional
