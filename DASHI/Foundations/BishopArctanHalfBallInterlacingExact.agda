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
-- Continue the concrete Machin arctangent construction by proving the actual
-- alternating-series interlacing on 0 <= x <= 1/2.  The ratio theorem from
-- BishopMachinArctanConstructionExact already gives m_(n+1) <= (1/4)m_n,
-- hence decreasing magnitudes.  Positive x identifies |x^(2n+1)| with the
-- unsigned power and the existing parity theorem handles the alternating sign.
------------------------------------------------------------------------

open import Agda.Builtin.Nat using (zero; suc)
open import Data.Rational.Unnormalised using (1ℚᵘ)

import Real as Bishop
import RealProperties as BishopP

import DASHI.Foundations.BishopMachinArctanConstructionExact as Atan
import DASHI.Physics.YangMills.BalabanClayGate4BishopHalfRadiusRealEstimatesExact as Estimates
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

quarterBelowOneNonStrict : Bishop._≤_ HalfBall.bishopQuarter Bishop.1ℝ
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
    termIndex = Alternating.double index
    exponent = Estimates.oddExponent termIndex
    coefficient = Bishop._⋆ (Atan.inverseOddRational termIndex)
    power = Bishop.pow value exponent
    powerNN = Concrete.powNonnegative (nonnegative point) exponent
  in
  BishopP.≃-trans
    (BishopP.*-cong
      (Concrete.alternatingSignEven index)
      (BishopP.*-congˡ
        (BishopP.≃-symm (BishopP.nonNegx⇒∣x∣≃x powerNN))))
    (BishopP.*-identityˡ
      (Bishop._*_ coefficient (Bishop.∣_∣ power)))

atanSignedOddIsNegativeMagnitude : ∀ {value} → PositiveHalfBallPoint value →
  ∀ index →
  Bishop._≃_
    (Atan.atanSignedTerm value (suc (Alternating.double index)))
    (Bishop.- Atan.atanMagnitudeTerm value (suc (Alternating.double index)))
atanSignedOddIsNegativeMagnitude {value} point index =
  let
    termIndex = suc (Alternating.double index)
    exponent = Estimates.oddExponent termIndex
    coefficient = Bishop._⋆ (Atan.inverseOddRational termIndex)
    power = Bishop.pow value exponent
    powerNN = Concrete.powNonnegative (nonnegative point) exponent
    magnitude = Atan.atanMagnitudeTerm value termIndex
  in
  BishopP.≃-trans
    (BishopP.*-cong
      (Concrete.alternatingSignOdd index)
      (BishopP.*-congˡ
        (BishopP.≃-symm (BishopP.nonNegx⇒∣x∣≃x powerNN))))
    (let open BishopP.ℝ-Solver
     in solve 1
        (λ m → (⊝ Κ 1ℚᵘ) ⊗ m ⊜ ⊝ m)
        BishopP.≃-refl magnitude)

atanAlternatingSeriesData : ∀ {value} →
  PositiveHalfBallPoint value →
  Alternating.AlternatingDecreasingSeriesData
atanAlternatingSeriesData {value} point = record
  { term = Atan.atanSignedTerm value
  ; magnitude = Atan.atanMagnitudeTerm value
  ; representedLimit = Atan.bishopAtanHalfBall value (insideHalf point)
  ; magnitudeNonnegative = Atan.atanMagnitudeNonnegative value
  ; magnitudeDecreasing = atanMagnitudeDecreasing point
  ; evenTermIsPositiveMagnitude = atanSignedEvenIsMagnitude point
  ; oddTermIsNegativeMagnitude = atanSignedOddIsNegativeMagnitude point
  ; seriesConvergesToRepresentedLimit =
      Atan.bishopAtanHalfBallConverges value (insideHalf point)
  }

atanInterlacing : ∀ {value} → PositiveHalfBallPoint value →
  Interlacing.BishopAlternatingInterlacingData
atanInterlacing point =
  Alternating.alternatingInterlacingData (atanAlternatingSeriesData point)

record ArctanCubicQuinticBracket (value : Bishop.ℝ) : Set₁ where
  field
    arctanValue : Bishop.ℝ
    lowerCubic : Bishop.ℝ
    upperQuintic : Bishop.ℝ
    lowerSound : lowerCubic Bishop.≤ arctanValue
    upperSound : arctanValue Bishop.≤ upperQuintic
open ArctanCubicQuinticBracket public

arctanCubicQuinticBracket : ∀ {value} →
  PositiveHalfBallPoint value → ArctanCubicQuinticBracket value
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
    ; lowerSound =
        Interlacing.lowerPartialBelowRepresentedLimit interlace (suc zero)
    ; upperSound =
        Interlacing.representedLimitBelowUpperPartial interlace (suc zero)
    }

bishopArctanAlternatingInterlacingLevel : ProofLevel
bishopArctanAlternatingInterlacingLevel = machineChecked

bishopArctanCubicQuinticBracketLevel : ProofLevel
bishopArctanCubicQuinticBracketLevel = machineChecked
