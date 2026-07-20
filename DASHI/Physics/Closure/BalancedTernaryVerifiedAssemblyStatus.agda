module DASHI.Physics.Closure.BalancedTernaryVerifiedAssemblyStatus where

open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.BalancedTernaryAnalyticCrossPollination as Cross

canonicalStatus : Cross.AnalyticStatus
canonicalStatus = Cross.currentAnalyticStatus

realSmoothificationRejected :
  Cross.realSmoothZ3Supported canonicalStatus ≡ false
realSmoothificationRejected = refl

pAdicAnalyticLaneOpen :
  Cross.pAdicAnalyticZ3Plausible canonicalStatus ≡ true
pAdicAnalyticLaneOpen = refl
