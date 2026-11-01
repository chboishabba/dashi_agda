module DASHI.Physics.Closure.NSTriadKNClayFrontierRound213Validation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.NSTriadKNClayFrontierRound213Exact as Frontier

resonantShellTriangleRegression :
  Frontier.round213ConcreteResonantOutputShellTriangleClosed ≡ true
resonantShellTriangleRegression = refl

twoSidedCollarRegression :
  Frontier.round213FixedOutputCCTwoSidedCollarClosed ≡ true
twoSidedCollarRegression = refl

constantBandPaymentStillOpenRegression :
  Frontier.round213ConstantBandSameOutputConvolutionPaymentClosed ≡ false
constantBandPaymentStillOpenRegression = refl

ccResidualStillOpenRegression :
  Frontier.round213PhysicalCCResidualBudgetClosed ≡ false
ccResidualStillOpenRegression = refl

packageAStillOpenRegression : Frontier.round213PackageAClosed ≡ false
packageAStillOpenRegression = refl

clayPromotionStillFalseRegression : Frontier.round213ClayPromotion ≡ false
clayPromotionStillFalseRegression = refl
