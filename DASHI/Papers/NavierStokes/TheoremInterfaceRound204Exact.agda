module DASHI.Papers.NavierStokes.TheoremInterfaceRound204Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound204Exact as R204

round204PaperComparableLocalizationClosed : Bool
round204PaperComparableLocalizationClosed =
  R204.round204ComparableShellLocalizationClosed

round204PaperLocalizedResidualPaymentClosed : Bool
round204PaperLocalizedResidualPaymentClosed =
  R204.round204LocalizedCCQuarticResidualPaymentClosed

round204PaperPackageAClosed : Bool
round204PaperPackageAClosed = R204.round204PackageAClosed

round204PaperClayPromotion : Bool
round204PaperClayPromotion = R204.round204ClayPromotion

round204PaperComparableLocalizationClosedIsTrue :
  round204PaperComparableLocalizationClosed ≡ true
round204PaperComparableLocalizationClosedIsTrue = refl

round204PaperLocalizedResidualPaymentClosedIsFalse :
  round204PaperLocalizedResidualPaymentClosed ≡ false
round204PaperLocalizedResidualPaymentClosedIsFalse = refl

round204PaperPackageAClosedIsFalse : round204PaperPackageAClosed ≡ false
round204PaperPackageAClosedIsFalse = refl

round204PaperClayPromotionIsFalse : round204PaperClayPromotion ≡ false
round204PaperClayPromotionIsFalse = refl
