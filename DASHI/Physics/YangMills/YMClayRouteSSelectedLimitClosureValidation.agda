{-# OPTIONS --safe #-}
module DASHI.Physics.YangMills.YMClayRouteSSelectedLimitClosureValidation where

open import Agda.Builtin.Equality using (_≡_)

import DASHI.Physics.YangMills.YMClayRouteSSelectedLimitClosureExact as H2c

terminalNeedsNoSequentialOrderClosureRecord :
  H2c.terminalRouteRequiresSequentialOrderClosureRecord ≡ false
terminalNeedsNoSequentialOrderClosureRecord =
  H2c.terminalRouteRequiresSequentialOrderClosureRecordIsFalse

terminalNeedsNoSameConvergenceWeld :
  H2c.terminalRouteRequiresSameConvergenceWeld ≡ false
terminalNeedsNoSameConvergenceWeld =
  H2c.terminalRouteRequiresSameConvergenceWeldIsFalse

terminalStillNeedsSelectedOneSidedClosure :
  H2c.terminalRouteRequiresSelectedLimitUpperClosure ≡ true
terminalStillNeedsSelectedOneSidedClosure =
  H2c.terminalRouteRequiresSelectedLimitUpperClosureIsTrue

selectedClosureIsNotFreshYMDecay :
  H2c.selectedLimitClosureIsFreshYMDecayEstimate ≡ false
selectedClosureIsNotFreshYMDecay =
  H2c.selectedLimitClosureIsFreshYMDecayEstimateIsFalse

r330CompatibilityRouteRemainsValid :
  H2c.strongerR330PackagingStillValidCompatibilityRoute ≡ true
r330CompatibilityRouteRemainsValid =
  H2c.strongerR330PackagingStillValidCompatibilityRouteIsTrue

promotionFailClosed :
  H2c.clayPromotion ≡ false
promotionFailClosed = H2c.clayPromotionIsFalse
