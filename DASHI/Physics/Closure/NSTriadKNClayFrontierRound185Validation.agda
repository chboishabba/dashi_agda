module DASHI.Physics.Closure.NSTriadKNClayFrontierRound185Validation where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Bool using (true; false)

import DASHI.Physics.Closure.NSTriadKNThreeClassFibreQuadraticRound184Exact as R184
import DASHI.Physics.Closure.NSTriadKNClasswisePartnerGramPaymentRound185Exact as R185
import DASHI.Physics.Closure.NSTriadKNClayFrontierRound185Exact as Frontier

crossClassDebtNotRequired : R184.round184CrossClassGramSignRequired ≡ false
crossClassDebtNotRequired = refl

threeClassConstantClosed : R184.round184UniversalClassCountConstant ≡ true
threeClassConstantClosed = refl

withinClassOnlyFrontier : R185.round185OnlyThreeWithinClassDebtsRemain ≡ true
withinClassOnlyFrontier = refl

noCardinalityFactor : R185.round185NoFibreCardinalityFactor ≡ true
noCardinalityFactor = refl

packageAStillOpen : Frontier.round185PackageAClosed ≡ false
packageAStillOpen = refl

noClayPromotion : Frontier.round185ClayPromotion ≡ false
noClayPromotion = refl
