module DASHI.Physics.Closure.NSTriadKNClayFrontierRound211Exact where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputUpperCollarRound210Exact as R210
import DASHI.Physics.Closure.NSTriadKNComparableOutputResidualPaymentRound211Exact as R211

round211BothCCInputsUpperLocalizedToFixedOutput : Bool
round211BothCCInputsUpperLocalizedToFixedOutput =
  R210.round210BothCCInputsUpperLocalizedToFixedOutput

round211BackwardResidualSocketExact : Bool
round211BackwardResidualSocketExact = R211.round211BackwardResidualSocketExact

round211ConcreteSameOutputResidualPaymentConstructed : Bool
round211ConcreteSameOutputResidualPaymentConstructed = false

round211PhysicalCCResidualBudgetClosed : Bool
round211PhysicalCCResidualBudgetClosed = false

round211PhysicalFLResidualBudgetClosed : Bool
round211PhysicalFLResidualBudgetClosed = false

round211PhysicalHHResidualBudgetClosed : Bool
round211PhysicalHHResidualBudgetClosed = false

round211PackageAClosed : Bool
round211PackageAClosed = false

round211ClayPromotion : Bool
round211ClayPromotion = false

round211BothCCInputsUpperLocalizedToFixedOutputIsTrue :
  round211BothCCInputsUpperLocalizedToFixedOutput ≡ true
round211BothCCInputsUpperLocalizedToFixedOutputIsTrue = refl

round211BackwardResidualSocketExactIsTrue :
  round211BackwardResidualSocketExact ≡ true
round211BackwardResidualSocketExactIsTrue = refl

round211ConcreteSameOutputResidualPaymentConstructedIsFalse :
  round211ConcreteSameOutputResidualPaymentConstructed ≡ false
round211ConcreteSameOutputResidualPaymentConstructedIsFalse = refl

round211PackageAClosedIsFalse : round211PackageAClosed ≡ false
round211PackageAClosedIsFalse = refl

round211ClayPromotionIsFalse : round211ClayPromotion ≡ false
round211ClayPromotionIsFalse = refl
