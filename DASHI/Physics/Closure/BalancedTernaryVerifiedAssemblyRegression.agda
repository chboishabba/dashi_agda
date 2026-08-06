module DASHI.Physics.Closure.BalancedTernaryVerifiedAssemblyRegression where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.BalancedTernaryAnalyticCrossPollination as Cross
import DASHI.Physics.Closure.BalancedTernaryVerifiedAssembly as Assembly

canonicalStatusIsShared :
  Assembly.canonicalStatus ≡ Cross.currentAnalyticStatus
canonicalStatusIsShared = refl

realSmoothificationRemainsRejected :
  Cross.realSmoothZ3Supported Assembly.canonicalStatus ≡ false
realSmoothificationRemainsRejected = refl

pAdicAnalyticLaneRemainsOpen :
  Cross.pAdicAnalyticZ3Plausible Assembly.canonicalStatus ≡ true
pAdicAnalyticLaneRemainsOpen = refl
