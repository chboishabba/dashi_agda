module DASHI.Physics.Closure.NSTriadKNClayFrontierRound209Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableFixedOutputCarrierRound207Exact as R207
import DASHI.Physics.Closure.NSTriadKNComparableOutputL2CarrierRound208Exact as R208
import DASHI.Physics.Closure.NSTriadKNComparableOutputGramTelescopeRound209Exact as R209
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound209Exact as Frontier

sameOutputScopingRegression :
  R207.round207ComparableGramScopedToOneOutput ≡ true
sameOutputScopingRegression = refl

crossOutputGramNotIntroducedRegression :
  R208.round208CrossOutputGramDebtIntroduced ≡ false
crossOutputGramNotIntroducedRegression = refl

outputwiseGramTelescopeRegression :
  R209.round209CrossOutputCovarianceEliminatedByCarrier ≡ true
outputwiseGramTelescopeRegression = refl

sameOutputDebtStillOpenRegression :
  Frontier.round209SameOutputComparableDebtQuantitativelyPaid ≡ false
sameOutputDebtStillOpenRegression = refl

physicalCCResidualBudgetStillOpenRegression :
  Frontier.round209PhysicalCCResidualBudgetClosed ≡ false
physicalCCResidualBudgetStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round209PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round209ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
