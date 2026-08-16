module DASHI.Foundations.BishopArctanHalfBallInterlacingExact where

------------------------------------------------------------------------
-- PRIMARY SOURCES
--
-- Errett Bishop and Douglas Bridges, "Constructive Analysis", Springer 1985.
-- DOI: 10.1007/978-3-642-61667-9.
--
-- Zachary Murray, "Constructive Analysis in the Agda Proof Assistant", 2022.
-- arXiv:2205.08354. No DOI assigned.
--
-- DASHI CONTRIBUTION
--
-- Continue the concrete Machin arctangent construction by proving the actual
-- alternating-series interlacing on 0 <= x <= 1/2.  The ratio theorem from
-- BishopMachinArctanConstructionExact already gives
--
--      m_(n+1) <= (1/4) m_n,
--
-- so magnitudes are decreasing.  Positive x identifies |x^(2n+1)| with the
-- unsigned power; the existing parity theorem identifies (-1)^(2n) and
-- (-1)^(2n+1).  Therefore the generic constructive alternating-series theorem
-- applies to the ACTUAL convergent arctangent series, not an abstract receipt.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (Nat; zero; suc)
open import Data.Rational.Unnormalised as ℚ using (1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanBishopConcreteHalfBallSquareExact as HalfBall
import DASHI.Physics.YangMills.BalabanBishopConcreteSineCosineInterlacingExact as Concrete
import DASHI.Physics.YangMills.BalabanBishopAlternatingInterlacingFromDecreasingTermsExact as Alternating
import DASHI.Physics.YangMills.BalabanBishopAlternatingBracketFromMonotoneLimitsExact as Interlacing
open import DASHI.Physics.YangMills.CompactLieProofLevel

record PositiveHalfBallPoint (value : Bishop.ℝ) : Set where
  constructor positiveHalfBallPoint
  field
    nonnegative : Bishop.NonNegative value
    insideHalf : Bishop._≤_ (Bishop.∣_∣ value) HalfBall.bishopHalf
open PositiveHalfBallPoint public

quarterBelowOneNonStrict :
  Bishop._≤_ HalfBall.bishopQuarter Bishop.1ℝ
quarterBelowOneNonStrict = BishopP.<⇒≤ Atan.quarterBelowOne

atanMagnitudeDecreasing : ∀ {value} → PositiveHalfBallPoint value →
  ∀ index →
  Bishop._≤_
    (Atan.atanMagnitudeTerm value (suc index))
    (Atan.atanMagnitudeTerm value index)
atanMagnitudeDecreasing {value} point index =
  BishopP.≤-trans
    (Atan.atanMagnitudeSuccessorBelowQuarter value index (insideHalf point))
    (BishopP.≤-respʳ-≃
      (BishopP.*-identityˡ (Atan.atanMagnitudeTerm value index))
      (BishopP.*-monoʳ-≤-nonNeg
        quarterBelowOneNonStrict
        (Atan.atanMagnitudeNonnegative value index)))

atanSignedEvenIsMagnitude : ∀ {value} → PositiveHalfBallPoint value →
  ∀ index →
  Bishop._≃_
    (Atan.atanSignedTerm value (Alternating.double index))
    (Atan.atanMagnitudeTerm value (Alternating.double index))
atanSignedEvenIsMagnitude {value} point index =
  let
    exponent = DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent
      (Alternating.double index)
    powerNN = Concrete.powNonnegative (nonnegative point) exponent
    absPower = BishopP.0≤x⇒∣x∣≃x (BishopP.nonNegx⇒0≤x powerNN)
  in
  BishopP.≃-trans
    (BishopP.*-congʳ
      (Bishop._*_
        (Bishop._⋆ (Atan.inverseOddRational (Alternating.double index)))
        (Bishop.pow value exponent))
      (Concrete.alternatingSignEven index))
    (BishopP.≃-trans
      (BishopP.*-identityˡ
        (Bishop._*_
          (Bishop._⋆ (Atan.inverseOddRational (Alternating.double index)))
          (Bishop.pow value exponent)))
      (BishopP.*-congˡ
        (Bishop._⋆ (Atan.inverseOddRational (Alternating.double index)))
        (BishopP.≃-symm absPower)))

atanSignedOddIsNegativeMagnitude : ∀ {value} → PositiveHalfBallPoint value →
  ∀ index →
  Bishop._≃_
    (Atan.atanSignedTerm value (suc (Alternating.double index)))
    (Bishop.- Atan.atanMagnitudeTerm value (suc (Alternating.double index)))
atanSignedOddIsNegativeMagnitude {value} point index =
  let
    position = suc (Alternating.double index)
    exponent = DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact.oddExponent position
    powerNN = Concrete.powNonnegative (nonnegative point) exponent
    absPower = BishopP.0≤x⇒∣x∣≃x (BishopP.nonNegx⇒0≤x powerNN)
    coefficient = Bishop._⋆ (Atan.inverseOddRational position)
    unsignedPower = Bishop.pow value exponent
    magnitude = Bishop._*_ coefficient (Bishop.∣_∣ unsignedPower)
  in
  BishopP.≃-trans
    (BishopP.*-congʳ
      (Bishop._*_ coefficient unsignedPower)
      (Concrete.alternatingSignOdd index))
    (BishopP.≃-trans
      (BishopP.negative-product-left (Bishop._*_ coefficient unsignedPower))
      (BishopP.neg-cong
        (BishopP.*-congˡ coefficient (BishopP.≃-symm absPower))))

atanAlternatingSeriesData : ∀ {value} →
  PositiveHalfBallPoint value →
  Alternating.AlternatingDecreasingSeriesData
atanAlternatingSeriesData {value} point = record
  { Alternating.AlternatingDecreasingSeriesData.term = Atan.atanSignedTerm value
  ; Alternating.AlternatingDecreasingSeriesData.magnitude = Atan.atanMagnitudeTerm value
  ; Alternating.AlternatingDecreasingSeriesData.representedLimit =
      Atan.bishopAtanHalfBall value (insideHalf point)
  ; Alternating.AlternatingDecreasingSeriesData.magnitudeNonnegative =
      Atan.atanMagnitudeNonnegative value
  ; Alternating.AlternatingDecreasingSeriesData.magnitudeDecreasing =
      atanMagnitudeDecreasing point
  ; Alternating.AlternatingDecreasingSeriesData.signedEvenIsMagnitude =
      atanSignedEvenIsMagnitude point
  ; Alternating.AlternatingDecreasingSeriesData.signedOddIsNegativeMagnitude =
      atanSignedOddIsNegativeMagnitude point
  ; Alternating.AlternatingDecreasingSeriesData.seriesConverges =
      Atan.bishopAtanHalfBallConverges value (insideHalf point)
  }

atanInterlacing : ∀ {value} → PositiveHalfBallPoint value →
  Interlacing.BishopAlternatingInterlacingData
atanInterlacing point =
  Alternating.alternatingInterlacing
    (atanAlternatingSeriesData point)

record ArctanCubicQuinticBracket (value : Bishop.ℝ) : Set₁ where
  field
    arctanValue : Bishop.ℝ
    lowerCubic : Bishop.ℝ
    upperQuintic : Bishop.ℝ
    lowerSound : lowerCubic Bishop.≤ arctanValue
    upperSound : arctanValue Bishop.≤ upperQuintic
open ArctanCubicQuinticBracket public

arctanCubicQuinticBracket : ∀ {value} →
  PositiveHalfBallPoint value →
  ArctanCubicQuinticBracket value
arctanCubicQuinticBracket {value} point =
  let
    dataSet = atanAlternatingSeriesData point
    interlace = atanInterlacing point
    lower = Alternating.lowerPartial dataSet (suc zero)
    upper = Alternating.upperPartial dataSet (suc zero)
  in
  record
    { arctanValue = Atan.bishopAtanHalfBall value (insideHalf point)
    ; lowerCubic = lower
    ; upperQuintic = upper
    ; lowerSound = Interlacing.lowerPartialBelowRepresentedLimit interlace (suc zero)
    ; upperSound = Interlacing.representedLimitBelowUpperPartial interlace (suc zero)
    }

bishopArctanAlternatingInterlacingLevel : ProofLevel
bishopArctanAlternatingInterlacingLevel = machineChecked

bishopArctanCubicQuinticBracketLevel : ProofLevel
bishopArctanCubicQuinticBracketLevel = machineChecked
