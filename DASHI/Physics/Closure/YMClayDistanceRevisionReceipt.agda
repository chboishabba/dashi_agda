module DASHI.Physics.Closure.YMClayDistanceRevisionReceipt where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

------------------------------------------------------------------------
-- Manager C3: YM Clay distance revision.

data YMClayDistanceRevised : Set where
  cuspUniversalityProof :
    YMClayDistanceRevised

data YMConformalClarification : Set where
  fourDimensionalYangMillsConformalInvarianceRecorded :
    YMConformalClarification

  carrierGeometryH3TimesRPlusNotH4 :
    YMConformalClarification

  conformalArgumentDoesNotFlattenCarrierSlices :
    YMConformalClarification

canonicalYMConformalClarifications : List YMConformalClarification
canonicalYMConformalClarifications =
  fourDimensionalYangMillsConformalInvarianceRecorded
  ∷ carrierGeometryH3TimesRPlusNotH4
  ∷ conformalArgumentDoesNotFlattenCarrierSlices
  ∷ []

ymCuspUniversalityStatement : String
ymCuspUniversalityStatement =
  "YM Clay distance is one geometric proof: YM in the flat cusp region of X_0(N), as N -> infinity, is in the universality class of Euclidean 4D SU(N) Yang-Mills."

data YMClayDistanceRevisionPromotion : Set where

ymClayDistanceRevisionPromotionImpossibleHere :
  YMClayDistanceRevisionPromotion →
  ⊥
ymClayDistanceRevisionPromotionImpossibleHere ()

record YMClayDistanceRevisionReceipt : Setω where
  field
    ymClayDistanceRevised :
      YMClayDistanceRevised

    ymClayDistanceRevisedIsCuspUniversality :
      ymClayDistanceRevised ≡ cuspUniversalityProof

    conformalInvarianceDoesNotApply :
      Bool

    conformalInvarianceDoesNotApplyIsTrue :
      conformalInvarianceDoesNotApply ≡ true

    carrierGeometry :
      String

    carrierGeometryIsH3TimesRPlus :
      carrierGeometry ≡ "H^3 x R+"

    hyperbolicFourSpacePoincareModel :
      String

    hyperbolicFourSpacePoincareModelIsNotCarrier :
      hyperbolicFourSpacePoincareModel ≡ "H^4 has flat R^3 slices in the Poincare model"

    cuspDegenerationBestCandidate :
      Bool

    cuspDegenerationBestCandidateIsTrue :
      cuspDegenerationBestCandidate ≡ true

    requiredProof :
      String

    requiredProofIsCanonical :
      requiredProof ≡ ymCuspUniversalityStatement

    clarifications :
      List YMConformalClarification

    clarificationsAreCanonical :
      clarifications ≡ canonicalYMConformalClarifications

    clayYangMillsPromoted :
      Bool

    clayYangMillsPromotedIsFalse :
      clayYangMillsPromoted ≡ false

    promotionFlags :
      List YMClayDistanceRevisionPromotion

    promotionFlagsAreEmpty :
      promotionFlags ≡ []

    receiptBoundary :
      List String

open YMClayDistanceRevisionReceipt public

canonicalYMClayDistanceRevisionReceipt :
  YMClayDistanceRevisionReceipt
canonicalYMClayDistanceRevisionReceipt =
  record
    { ymClayDistanceRevised =
        cuspUniversalityProof
    ; ymClayDistanceRevisedIsCuspUniversality =
        refl
    ; conformalInvarianceDoesNotApply =
        true
    ; conformalInvarianceDoesNotApplyIsTrue =
        refl
    ; carrierGeometry =
        "H^3 x R+"
    ; carrierGeometryIsH3TimesRPlus =
        refl
    ; hyperbolicFourSpacePoincareModel =
        "H^4 has flat R^3 slices in the Poincare model"
    ; hyperbolicFourSpacePoincareModelIsNotCarrier =
        refl
    ; cuspDegenerationBestCandidate =
        true
    ; cuspDegenerationBestCandidateIsTrue =
        refl
    ; requiredProof =
        ymCuspUniversalityStatement
    ; requiredProofIsCanonical =
        refl
    ; clarifications =
        canonicalYMConformalClarifications
    ; clarificationsAreCanonical =
        refl
    ; clayYangMillsPromoted =
        false
    ; clayYangMillsPromotedIsFalse =
        refl
    ; promotionFlags =
        []
    ; promotionFlagsAreEmpty =
        refl
    ; receiptBoundary =
        "Manager C3 records that conformal invariance does not resolve the carrier archimedean gap"
        ∷ "The remaining YM task is cusp-region universality for Euclidean 4D SU(N) YM"
        ∷ "No Clay Yang-Mills promotion is made"
        ∷ []
    }

canonicalYMClayDistanceRevisionKeepsClayFalse :
  clayYangMillsPromoted canonicalYMClayDistanceRevisionReceipt ≡ false
canonicalYMClayDistanceRevisionKeepsClayFalse =
  refl

canonicalYMClayDistanceRevisionNoPromotion :
  YMClayDistanceRevisionPromotion →
  ⊥
canonicalYMClayDistanceRevisionNoPromotion =
  ymClayDistanceRevisionPromotionImpossibleHere
