module DASHI.Physics.Closure.NSTriadKNClayFrontierRound205Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableRawCurlPartnerMassRound205Exact as Producer
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound205Exact as Frontier

localizedComparableRawCurlPartnerConstructedRegression :
  Producer.round205ActualLocalizedCCRawCurlPartnerConstructed ≡ true
localizedComparableRawCurlPartnerConstructedRegression = refl

localizedComparablePartnerMassBoundRegression :
  Producer.round205LocalizedCCPartnerMassBoundClosed ≡ true
localizedComparablePartnerMassBoundRegression = refl

shellCountNotIntroducedRegression :
  Producer.round205LocalizedCCPartnerMassIntroducesShellCount ≡ false
shellCountNotIntroducedRegression = refl

betweenPartnerCovarianceStillOpenRegression :
  Frontier.round205LocalizedCCBetweenPartnerCovariancePaid ≡ false
betweenPartnerCovarianceStillOpenRegression = refl

physicalCCResidualBudgetStillOpenRegression :
  Frontier.round205PhysicalCCResidualBudgetClosed ≡ false
physicalCCResidualBudgetStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round205PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round205ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
