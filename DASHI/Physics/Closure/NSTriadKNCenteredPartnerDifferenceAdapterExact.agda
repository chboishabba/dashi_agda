module DASHI.Physics.Closure.NSTriadKNCenteredPartnerDifferenceAdapterExact where

------------------------------------------------------------------------
-- R205 -> R574/R446 SAME-OBJECT PARTNER-DIFFERENCE ADAPTER
--
-- R205 owns the literal localized comparable raw-curl partner block and R181
-- compresses that block to one physical Complex3 cell by pairCell.  R574 owns
-- a completely generic two-vector difference carrier and sends its difference
-- to R446's positive-rate Hermitian Cauchy PSD carrier.
--
-- This file specializes those generic constructions to two actual R205
-- compressed partner cells.  The key point is purely same-object:
--
--   value (R574.toDifferenceCell574 (... alpha beta ...))
--     = pairCell(R205.comparablePartnerCell alpha)
--       - pairCell(R205.comparablePartnerCell beta).
--
-- No norm estimate, radial/Pluecker estimate, centered second-moment estimate,
-- cutoff aggregation, spacetime estimate, or Clay promotion is introduced.
-- The next genuine analytic splice is to identify this literal difference with
-- the existing R128/R176 radial-directional defect coordinates strongly enough
-- to construct the old CenteredPairCell carrier.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; Positive)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3GalerkinEquationAudit as Audit
import DASHI.Physics.Closure.NSTriadKNPartnerBlockGramLedgerRound181Exact as R181
import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as R205
import DASHI.Physics.Closure.NSTriadKNRationalComplex3CauchyPSDRound446Exact as R446
import DASHI.Physics.Closure.NSTriadKNCauchyVectorPolarizationRound574Exact as R574

F = R205.F

compressedPartnerVector :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system → C3.Complex3 F
compressedPartnerVector partner =
  R181.pairCell (R205.comparablePartnerCell partner)

compressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system →
  C3.Complex3 F
compressedPartnerDifference alpha beta =
  C3.complex3Subtract
    (compressedPartnerVector alpha)
    (compressedPartnerVector beta)

toR574PartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I} →
  (rate : ℚ) →
  Positive rate →
  R205.LocalizedComparableRawCurlPartner system →
  R205.LocalizedComparableRawCurlPartner system →
  R574.CauchyVectorPairCell574
toR574PartnerDifference rate ratePositive alpha beta =
  R574.cauchy-vector-pair-cell-574
    rate
    (compressedPartnerVector alpha)
    (compressedPartnerVector beta)
    ratePositive

r574DifferenceIsCompressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  C3.complex3Subtract
    (R574.left574
      (toR574PartnerDifference rate ratePositive alpha beta))
    (R574.right574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ compressedPartnerDifference alpha beta
r574DifferenceIsCompressedPartnerDifference rate ratePositive alpha beta = refl

r446DifferenceValueIsCompressedPartnerDifference :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  R446.value
    (R574.toDifferenceCell574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ compressedPartnerDifference alpha beta
r446DifferenceValueIsCompressedPartnerDifference rate ratePositive alpha beta = refl

r446DifferenceRateIsSelectedRate :
  ∀ {E : C3.IntegerEmbedding F}
    {I : C3.ModeInverseSquare F E}
    {system : Audit.FiniteComplex3GalerkinSystem F E I}
    (rate : ℚ)
    (ratePositive : Positive rate)
    (alpha beta : R205.LocalizedComparableRawCurlPartner system) →
  R446.rate
    (R574.toDifferenceCell574
      (toR574PartnerDifference rate ratePositive alpha beta))
  ≡ rate
r446DifferenceRateIsSelectedRate rate ratePositive alpha beta = refl

------------------------------------------------------------------------
-- Fail-closed status.
------------------------------------------------------------------------

roundCenteredPartnerR205ToR574DifferenceSameObjectClosed : Bool
roundCenteredPartnerR205ToR574DifferenceSameObjectClosed = true

roundCenteredPartnerR574ToR446DifferenceSameObjectClosed : Bool
roundCenteredPartnerR574ToR446DifferenceSameObjectClosed = true

roundCenteredPartnerRadialPlueckerDefectWeldClosed : Bool
roundCenteredPartnerRadialPlueckerDefectWeldClosed = false

roundCenteredPartnerCenteredPairCellConstructed : Bool
roundCenteredPartnerCenteredPairCellConstructed = false

roundCenteredPartnerCutoffUniformAggregateClosed : Bool
roundCenteredPartnerCutoffUniformAggregateClosed = false

roundCenteredPartnerClayPromotion : Bool
roundCenteredPartnerClayPromotion = false

roundCenteredPartnerR205ToR574DifferenceSameObjectClosedIsTrue :
  roundCenteredPartnerR205ToR574DifferenceSameObjectClosed ≡ true
roundCenteredPartnerR205ToR574DifferenceSameObjectClosedIsTrue = refl

roundCenteredPartnerR574ToR446DifferenceSameObjectClosedIsTrue :
  roundCenteredPartnerR574ToR446DifferenceSameObjectClosed ≡ true
roundCenteredPartnerR574ToR446DifferenceSameObjectClosedIsTrue = refl

roundCenteredPartnerRadialPlueckerDefectWeldClosedIsFalse :
  roundCenteredPartnerRadialPlueckerDefectWeldClosed ≡ false
roundCenteredPartnerRadialPlueckerDefectWeldClosedIsFalse = refl

roundCenteredPartnerClayPromotionIsFalse :
  roundCenteredPartnerClayPromotion ≡ false
roundCenteredPartnerClayPromotionIsFalse = refl
