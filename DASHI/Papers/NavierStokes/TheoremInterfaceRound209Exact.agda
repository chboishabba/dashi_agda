module DASHI.Papers.NavierStokes.TheoremInterfaceRound209Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound209Exact as R209

round209PaperComparableGramScopedToOneOutput : Bool
round209PaperComparableGramScopedToOneOutput =
  R209.round209ComparableGramScopedToOneOutput

round209PaperCrossOutputCovarianceEliminated : Bool
round209PaperCrossOutputCovarianceEliminated =
  R209.round209CrossOutputCovarianceEliminatedByCarrier

round209PaperSameOutputDebtPaid : Bool
round209PaperSameOutputDebtPaid =
  R209.round209SameOutputComparableDebtQuantitativelyPaid

round209PaperPhysicalCCResidualBudgetClosed : Bool
round209PaperPhysicalCCResidualBudgetClosed =
  R209.round209PhysicalCCResidualBudgetClosed

round209PaperPackageAClosed : Bool
round209PaperPackageAClosed = R209.round209PackageAClosed

round209PaperClayPromotion : Bool
round209PaperClayPromotion = R209.round209ClayPromotion

round209PaperComparableGramScopedToOneOutputIsTrue :
  round209PaperComparableGramScopedToOneOutput ≡ true
round209PaperComparableGramScopedToOneOutputIsTrue = refl

round209PaperCrossOutputCovarianceEliminatedIsTrue :
  round209PaperCrossOutputCovarianceEliminated ≡ true
round209PaperCrossOutputCovarianceEliminatedIsTrue = refl

round209PaperSameOutputDebtPaidIsFalse :
  round209PaperSameOutputDebtPaid ≡ false
round209PaperSameOutputDebtPaidIsFalse = refl

round209PaperPackageAClosedIsFalse : round209PaperPackageAClosed ≡ false
round209PaperPackageAClosedIsFalse = refl

round209PaperClayPromotionIsFalse : round209PaperClayPromotion ≡ false
round209PaperClayPromotionIsFalse = refl
