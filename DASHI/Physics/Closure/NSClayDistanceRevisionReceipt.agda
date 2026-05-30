module DASHI.Physics.Closure.NSClayDistanceRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C2: NS Clay distance revision.
--
-- The previous contraction framing is retired.  The current candidate is
-- an H^{11/8} global energy bound built from bandwise estimates.

data NSClayDistanceRevised : Set where
  bernoulliBandArgument :
    NSClayDistanceRevised

data NSGlobalBoundIngredient : Set where
  lerayL2BandBound :
    NSGlobalBoundIngredient

  dissipationCutoffJNu :
    NSGlobalBoundIngredient

  bernoulliUpwardCascade :
    NSGlobalBoundIngredient

  highBandGeometricSeries :
    NSGlobalBoundIngredient

  prodiSerrinSmoothnessPassage :
    NSGlobalBoundIngredient

canonicalNSGlobalBoundIngredients : List NSGlobalBoundIngredient
canonicalNSGlobalBoundIngredients =
  lerayL2BandBound
  ∷ dissipationCutoffJNu
  ∷ bernoulliUpwardCascade
  ∷ highBandGeometricSeries
  ∷ prodiSerrinSmoothnessPassage
  ∷ []

data NSRemainingAnalyticGap : Set where
  makeBernoulliBandArgumentRigorous :
    NSRemainingAnalyticGap

  checkSobolevConstantsAgainstGeometricSeries :
    NSRemainingAnalyticGap

canonicalNSRemainingAnalyticGaps : List NSRemainingAnalyticGap
canonicalNSRemainingAnalyticGaps =
  makeBernoulliBandArgumentRigorous
  ∷ checkSobolevConstantsAgainstGeometricSeries
  ∷ []

nsRevisedDistanceStatement : String
nsRevisedDistanceStatement =
  "NS Clay distance is the Bernoulli band argument: Leray L2 band bound plus dissipation cutoff plus upward Bernoulli cascade plus geometric high-band sum; if rigorous, the global H^{11/8} bound feeds Prodi-Serrin smoothness."

data NSClayDistanceRevisionPromotion : Set where

nsClayDistanceRevisionPromotionImpossibleHere :
  NSClayDistanceRevisionPromotion →
  ⊥
nsClayDistanceRevisionPromotionImpossibleHere ()

record NSClayDistanceRevisionReceipt : Setω where
  field
    nsClayDistanceRevised :
      NSClayDistanceRevised

    nsClayDistanceRevisedIsBernoulli :
      nsClayDistanceRevised ≡ bernoulliBandArgument

    previousContractionFramingRetired :
      Bool

    previousContractionFramingRetiredIsTrue :
      previousContractionFramingRetired ≡ true

    globalH118BoundCandidate :
      Bool

    globalH118BoundCandidateIsTrue :
      globalH118BoundCandidate ≡ true

    sobolevNumerator :
      Nat

    sobolevNumeratorIs11 :
      sobolevNumerator ≡ 11

    sobolevDenominator :
      Nat

    sobolevDenominatorIs8 :
      sobolevDenominator ≡ 8

    ingredients :
      List NSGlobalBoundIngredient

    ingredientsAreCanonical :
      ingredients ≡ canonicalNSGlobalBoundIngredients

    gapCount :
      Nat

    gapCountIsTwoAnalyticChecks :
      gapCount ≡ 2

    remainingGaps :
      List NSRemainingAnalyticGap

    remainingGapsAreCanonical :
      remainingGaps ≡ canonicalNSRemainingAnalyticGaps

    prodiSerrinPassageRecorded :
      Bool

    prodiSerrinPassageRecordedIsTrue :
      prodiSerrinPassageRecorded ≡ true

    clayNavierStokesPromoted :
      Bool

    clayNavierStokesPromotedIsFalse :
      clayNavierStokesPromoted ≡ false

    statement :
      String

    statementIsCanonical :
      statement ≡ nsRevisedDistanceStatement

    promotionFlags :
      List NSClayDistanceRevisionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open NSClayDistanceRevisionReceipt public

canonicalNSClayDistanceRevisionReceipt :
  NSClayDistanceRevisionReceipt
canonicalNSClayDistanceRevisionReceipt =
  record
    { nsClayDistanceRevised =
        bernoulliBandArgument
    ; nsClayDistanceRevisedIsBernoulli =
        refl
    ; previousContractionFramingRetired =
        true
    ; previousContractionFramingRetiredIsTrue =
        refl
    ; globalH118BoundCandidate =
        true
    ; globalH118BoundCandidateIsTrue =
        refl
    ; sobolevNumerator =
        11
    ; sobolevNumeratorIs11 =
        refl
    ; sobolevDenominator =
        8
    ; sobolevDenominatorIs8 =
        refl
    ; ingredients =
        canonicalNSGlobalBoundIngredients
    ; ingredientsAreCanonical =
        refl
    ; gapCount =
        2
    ; gapCountIsTwoAnalyticChecks =
        refl
    ; remainingGaps =
        canonicalNSRemainingAnalyticGaps
    ; remainingGapsAreCanonical =
        refl
    ; prodiSerrinPassageRecorded =
        true
    ; prodiSerrinPassageRecordedIsTrue =
        refl
    ; clayNavierStokesPromoted =
        false
    ; clayNavierStokesPromotedIsFalse =
        refl
    ; statement =
        nsRevisedDistanceStatement
    ; statementIsCanonical =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager C2 retires the large-data contraction framing"
        ∷ "The remaining NS task is the rigorous Bernoulli band argument"
        ∷ "This receipt records a candidate route only, not a Clay promotion"
        ∷ []
    }

canonicalNSClayDistanceRevisionKeepsClayFalse :
  clayNavierStokesPromoted canonicalNSClayDistanceRevisionReceipt ≡ false
canonicalNSClayDistanceRevisionKeepsClayFalse =
  refl

canonicalNSClayDistanceRevisionNoPromotion :
  NSClayDistanceRevisionPromotion →
  ⊥
canonicalNSClayDistanceRevisionNoPromotion =
  nsClayDistanceRevisionPromotionImpossibleHere
