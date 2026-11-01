module DASHI.Physics.Closure.NSTriadKNClayFrontierRound202Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNBlockGramResidualBudgetRound202Exact as R202
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound202Exact as Frontier

gramNegativityNotRequired : R202.round202GramNegativityRequired ≡ false
gramNegativityNotRequired = refl

positiveResidualCovarianceAllowed :
  R202.round202PositiveResidualCovarianceAdmissible ≡ true
positiveResidualCovarianceAllowed = refl

quantitativeResidualCompilerClosed :
  R202.round202QuantitativeBlockResidualCompilerClosed ≡ true
quantitativeResidualCompilerClosed = refl

packageAStillOpen : Frontier.round202PackageAClosed ≡ false
packageAStillOpen = refl

noClayPromotion : Frontier.round202ClayPromotion ≡ false
noClayPromotion = refl
