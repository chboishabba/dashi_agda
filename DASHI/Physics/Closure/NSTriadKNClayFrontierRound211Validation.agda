module DASHI.Physics.Closure.NSTriadKNClayFrontierRound211Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputUpperCollarRound210Exact as R210
import DASHI.Physics.Closure.NSTriadKNComparableOutputResidualPaymentRound211Exact as R211
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound211Exact as Frontier

upperCollarRegression :
  R210.round210BothCCInputsUpperLocalizedToFixedOutput ≡ true
upperCollarRegression = refl

noFakeLowerCollarRegression :
  R210.round210IntroducesLowerShellCollar ≡ false
noFakeLowerCollarRegression = refl

noCutoffShellCountRegression :
  R210.round210IntroducesCutoffShellCount ≡ false
noCutoffShellCountRegression = refl

backwardSocketRegression :
  R211.round211BackwardResidualSocketExact ≡ true
backwardSocketRegression = refl

noGramNegativityRequirementRegression :
  R211.round211RequiresGramNegativity ≡ false
noGramNegativityRequirementRegression = refl

concretePaymentStillOpenRegression :
  Frontier.round211ConcreteSameOutputResidualPaymentConstructed ≡ false
concretePaymentStillOpenRegression = refl

ccBudgetStillOpenRegression :
  Frontier.round211PhysicalCCResidualBudgetClosed ≡ false
ccBudgetStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round211PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round211ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
