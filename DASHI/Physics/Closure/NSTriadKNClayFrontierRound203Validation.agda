module DASHI.Physics.Closure.NSTriadKNClayFrontierRound203Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNComparableShellLocalizationRound203Exact as Local
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound203Exact as Frontier

comparableInputPairLocalizedRegression :
  Local.round203ComparableInputPairLocalized ≡ true
comparableInputPairLocalizedRegression = refl

comparableOutputAnchorRegression :
  Local.round203ComparableAnchoredToOutputOnOneInput ≡ true
comparableOutputAnchorRegression = refl

ccLocalizationClosedRegression :
  Frontier.round203PhysicalCCShellLocalizationClosed ≡ true
ccLocalizationClosedRegression = refl

ccResidualBudgetStillOpenRegression :
  Frontier.round203PhysicalCCResidualBudgetClosed ≡ false
ccResidualBudgetStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round203PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round203ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
