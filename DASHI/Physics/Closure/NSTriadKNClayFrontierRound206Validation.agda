module DASHI.Physics.Closure.NSTriadKNClayFrontierRound206Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparablePartnerGramFrontierRound206Exact as Producer
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound206Exact as Frontier

finiteLocalizedCarrierConstructedRegression :
  Producer.round206LocalizedCCFinitePartnerCarrierConstructed ≡ true
finiteLocalizedCarrierConstructedRegression = refl

exactCompressedGramLedgerRegression :
  Producer.round206LocalizedCCExactCompressedGramLedgerClosed ≡ true
exactCompressedGramLedgerRegression = refl

abstractCarrierGapGoneRegression :
  Producer.round206LocalizedCCAbstractCarrierGapRemains ≡ false
abstractCarrierGapGoneRegression = refl

betweenPartnerDebtStillOpenRegression :
  Frontier.round206LocalizedCCBetweenPartnerDebtQuantitativelyPaid ≡ false
betweenPartnerDebtStillOpenRegression = refl

physicalCCResidualBudgetStillOpenRegression :
  Frontier.round206PhysicalCCResidualBudgetClosed ≡ false
physicalCCResidualBudgetStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round206PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round206ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
