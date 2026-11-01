module DASHI.Papers.NavierStokes.TheoremInterfaceRound203Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound203Exact as R203

round203PaperComparableShellLocalizationClosed : Bool
round203PaperComparableShellLocalizationClosed =
  R203.round203PhysicalCCShellLocalizationClosed

round203PaperComparableResidualBudgetClosed : Bool
round203PaperComparableResidualBudgetClosed =
  R203.round203PhysicalCCResidualBudgetClosed

round203PaperPackageAClosed : Bool
round203PaperPackageAClosed = R203.round203PackageAClosed

round203PaperClayPromotion : Bool
round203PaperClayPromotion = R203.round203ClayPromotion

round203PaperComparableShellLocalizationClosedIsTrue :
  round203PaperComparableShellLocalizationClosed ≡ true
round203PaperComparableShellLocalizationClosedIsTrue = refl

round203PaperComparableResidualBudgetClosedIsFalse :
  round203PaperComparableResidualBudgetClosed ≡ false
round203PaperComparableResidualBudgetClosedIsFalse = refl

round203PaperPackageAClosedIsFalse : round203PaperPackageAClosed ≡ false
round203PaperPackageAClosedIsFalse = refl

round203PaperClayPromotionIsFalse : round203PaperClayPromotion ≡ false
round203PaperClayPromotionIsFalse = refl
