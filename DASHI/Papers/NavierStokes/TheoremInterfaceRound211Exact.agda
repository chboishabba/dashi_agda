module DASHI.Papers.NavierStokes.TheoremInterfaceRound211Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound211Exact as R211

round211PaperBothInputsUpperLocalized : Bool
round211PaperBothInputsUpperLocalized =
  R211.round211BothCCInputsUpperLocalizedToFixedOutput

round211PaperBackwardResidualSocketExact : Bool
round211PaperBackwardResidualSocketExact =
  R211.round211BackwardResidualSocketExact

round211PaperConcreteResidualPaymentConstructed : Bool
round211PaperConcreteResidualPaymentConstructed =
  R211.round211ConcreteSameOutputResidualPaymentConstructed

round211PaperPhysicalCCResidualBudgetClosed : Bool
round211PaperPhysicalCCResidualBudgetClosed =
  R211.round211PhysicalCCResidualBudgetClosed

round211PaperPackageAClosed : Bool
round211PaperPackageAClosed = R211.round211PackageAClosed

round211PaperClayPromotion : Bool
round211PaperClayPromotion = R211.round211ClayPromotion

round211PaperBothInputsUpperLocalizedIsTrue :
  round211PaperBothInputsUpperLocalized ≡ true
round211PaperBothInputsUpperLocalizedIsTrue = refl

round211PaperBackwardResidualSocketExactIsTrue :
  round211PaperBackwardResidualSocketExact ≡ true
round211PaperBackwardResidualSocketExactIsTrue = refl

round211PaperConcreteResidualPaymentConstructedIsFalse :
  round211PaperConcreteResidualPaymentConstructed ≡ false
round211PaperConcreteResidualPaymentConstructedIsFalse = refl

round211PaperPackageAClosedIsFalse : round211PaperPackageAClosed ≡ false
round211PaperPackageAClosedIsFalse = refl

round211PaperClayPromotionIsFalse : round211PaperClayPromotion ≡ false
round211PaperClayPromotionIsFalse = refl
