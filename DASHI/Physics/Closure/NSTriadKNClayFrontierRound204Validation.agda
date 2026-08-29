module DASHI.Physics.Closure.NSTriadKNClayFrontierRound204Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableResidualProducerBoundaryRound204Exact as Producer
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound204Exact as Frontier

literalCertificateFeedsLocalizationRegression :
  Producer.round204LiteralCCCertificateFeedsLocalization ≡ true
literalCertificateFeedsLocalizationRegression = refl

strongerComparabilityAssumptionNotNeededRegression :
  Producer.round204IndependentStrongerComparabilityAssumptionNeeded ≡ false
strongerComparabilityAssumptionNotNeededRegression = refl

localizedResidualPaymentStillOpenRegression :
  Frontier.round204LocalizedCCQuarticResidualPaymentClosed ≡ false
localizedResidualPaymentStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round204PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round204ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
