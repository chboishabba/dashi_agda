module DASHI.Physics.Closure.Deg23ResidualDiagnosticReceipt where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Float using (Float)
open import Agda.Builtin.Nat using (Nat; _+_)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- deg23 residual diagnostic receipt.
--
-- This is a concrete non-promoting receipt.  It records the natural carrier
-- readback
--
--   deg23 = |E(F5)| + |E(F7)| = 6 + 8 = 14
--
-- against the required diagnostic exact value 14.302.  The gap is recorded as
-- 0.302 / 14.302, about 2.1 percent.  The RG-running explanation is preserved
-- as an open hypothesis only; no Standard-Model, empirical-adequacy, or
-- closure-promotion flag is emitted.

data Deg23ResidualStatus : Set where
  naturalDeg23ResidualAgainstRequiredDiagnostic :
    Deg23ResidualStatus

data Deg23RGRunningHypothesisStatus : Set where
  rgRunningHypothesisOpen :
    Deg23RGRunningHypothesisStatus

data Deg23PromotionFlag : Set where

deg23PromotionFlagImpossibleHere :
  Deg23PromotionFlag →
  ⊥
deg23PromotionFlagImpossibleHere ()

record Deg23ResidualDiagnosticReceipt : Set where
  field
    status :
      Deg23ResidualStatus

    eF5Label :
      String

    eF5PointCount :
      Nat

    eF5PointCountIsSix :
      eF5PointCount ≡ 6

    eF7Label :
      String

    eF7PointCount :
      Nat

    eF7PointCountIsEight :
      eF7PointCount ≡ 8

    naturalDeg23 :
      Nat

    naturalDeg23IsPointCountSum :
      naturalDeg23 ≡ eF5PointCount + eF7PointCount

    naturalDeg23IsFourteen :
      naturalDeg23 ≡ 14

    requiredDiagnosticExact :
      Float

    requiredDiagnosticExactDecimal :
      String

    requiredDiagnosticExactMilli :
      Nat

    requiredDiagnosticExactMilliIs14302 :
      requiredDiagnosticExactMilli ≡ 14302

    naturalDeg23Milli :
      Nat

    naturalDeg23MilliIs14000 :
      naturalDeg23Milli ≡ 14000

    residualMilli :
      Nat

    residualMilliIs302 :
      residualMilli ≡ 302

    residualRatioLabel :
      String

    residualPercentApproxLabel :
      String

    residualPercentBasisPointsRounded :
      Nat

    residualPercentBasisPointsRoundedIs211 :
      residualPercentBasisPointsRounded ≡ 211

    rgRunningHypothesis :
      Deg23RGRunningHypothesisStatus

    rgRunningHypothesisRecorded :
      Bool

    rgRunningHypothesisRecordedIsTrue :
      rgRunningHypothesisRecorded ≡ true

    rgRunningHypothesisClosed :
      Bool

    rgRunningHypothesisClosedIsFalse :
      rgRunningHypothesisClosed ≡ false

    empiricalAdequacyPromoted :
      Bool

    empiricalAdequacyPromotedIsFalse :
      empiricalAdequacyPromoted ≡ false

    standardModelPromotionFlag :
      Bool

    standardModelPromotionFlagIsFalse :
      standardModelPromotionFlag ≡ false

    closurePromotionFlag :
      Bool

    closurePromotionFlagIsFalse :
      closurePromotionFlag ≡ false

    promotionFlags :
      List Deg23PromotionFlag

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open Deg23ResidualDiagnosticReceipt public

canonicalDeg23ResidualDiagnosticReceipt :
  Deg23ResidualDiagnosticReceipt
canonicalDeg23ResidualDiagnosticReceipt =
  record
    { status =
        naturalDeg23ResidualAgainstRequiredDiagnostic
    ; eF5Label =
        "|E(F5)|"
    ; eF5PointCount =
        6
    ; eF5PointCountIsSix =
        refl
    ; eF7Label =
        "|E(F7)|"
    ; eF7PointCount =
        8
    ; eF7PointCountIsEight =
        refl
    ; naturalDeg23 =
        14
    ; naturalDeg23IsPointCountSum =
        refl
    ; naturalDeg23IsFourteen =
        refl
    ; requiredDiagnosticExact =
        14.302
    ; requiredDiagnosticExactDecimal =
        "14.302"
    ; requiredDiagnosticExactMilli =
        14302
    ; requiredDiagnosticExactMilliIs14302 =
        refl
    ; naturalDeg23Milli =
        14000
    ; naturalDeg23MilliIs14000 =
        refl
    ; residualMilli =
        302
    ; residualMilliIs302 =
        refl
    ; residualRatioLabel =
        "residual = (14.302 - 14) / 14.302 = 0.302 / 14.302"
    ; residualPercentApproxLabel =
        "residual approximately 2.1 percent"
    ; residualPercentBasisPointsRounded =
        211
    ; residualPercentBasisPointsRoundedIs211 =
        refl
    ; rgRunningHypothesis =
        rgRunningHypothesisOpen
    ; rgRunningHypothesisRecorded =
        true
    ; rgRunningHypothesisRecordedIsTrue =
        refl
    ; rgRunningHypothesisClosed =
        false
    ; rgRunningHypothesisClosedIsFalse =
        refl
    ; empiricalAdequacyPromoted =
        false
    ; empiricalAdequacyPromotedIsFalse =
        refl
    ; standardModelPromotionFlag =
        false
    ; standardModelPromotionFlagIsFalse =
        refl
    ; closurePromotionFlag =
        false
    ; closurePromotionFlagIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "natural deg23 readback is |E(F5)| + |E(F7)| = 6 + 8 = 14"
        ∷ "required diagnostic exact value is 14.302"
        ∷ "absolute residual is 0.302, recorded exactly as 302 milli-units"
        ∷ "relative residual is approximately 2.1 percent"
        ∷ "RG-running is recorded only as an open hypothesis"
        ∷ "no empirical adequacy, Standard Model, or closure promotion flag is emitted"
        ∷ []
    }

deg23NaturalValueIsFourteen :
  naturalDeg23 canonicalDeg23ResidualDiagnosticReceipt ≡ 14
deg23NaturalValueIsFourteen =
  refl

deg23RequiredDiagnosticExactMilliIs14302 :
  requiredDiagnosticExactMilli canonicalDeg23ResidualDiagnosticReceipt
  ≡
  14302
deg23RequiredDiagnosticExactMilliIs14302 =
  refl

deg23ResidualPercentRoundedIsApproximatelyTwoPointOnePercent :
  residualPercentBasisPointsRounded canonicalDeg23ResidualDiagnosticReceipt
  ≡
  211
deg23ResidualPercentRoundedIsApproximatelyTwoPointOnePercent =
  refl

deg23RGRunningHypothesisStillOpen :
  rgRunningHypothesisClosed canonicalDeg23ResidualDiagnosticReceipt
  ≡
  false
deg23RGRunningHypothesisStillOpen =
  refl

deg23NoPromotionFlags :
  promotionFlags canonicalDeg23ResidualDiagnosticReceipt
  ≡
  []
deg23NoPromotionFlags =
  refl
