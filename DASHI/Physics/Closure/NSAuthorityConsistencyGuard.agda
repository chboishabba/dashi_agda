module DASHI.Physics.Closure.NSAuthorityConsistencyGuard where

open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Physics.Closure.ClayNSCurrentStateReceipt as Current
import DASHI.Physics.Closure.NSRegularityGapReceipt as Gap

------------------------------------------------------------------------
-- Promotion guard for mixed-scope NS receipts.
--
-- Current-scope receipts may record a modeled/global-regularity result while
-- the continuum BKM passage remains open. The latter, together with the Clay
-- authority flag, controls promotion. This guard makes that boundary explicit.

record NSAuthorityConsistencyGuard : Set where
  constructor mkNSAuthorityConsistencyGuard
  field
    currentScopeGlobalRegularity : Bool
    currentScopeGlobalRegularityIsTrue :
      currentScopeGlobalRegularity ≡ true

    continuumBKMClosed : Bool
    continuumBKMClosedIsFalse : continuumBKMClosed ≡ false

    clayPromotion : Bool
    clayPromotionIsFalse : clayPromotion ≡ false

    scopeConflictDetected : Bool
    scopeConflictDetectedIsTrue : scopeConflictDetected ≡ true

    promotionGuard : Bool
    promotionGuardIsFalse : promotionGuard ≡ false

open NSAuthorityConsistencyGuard public

canonicalNSAuthorityConsistencyGuard : NSAuthorityConsistencyGuard
canonicalNSAuthorityConsistencyGuard =
  mkNSAuthorityConsistencyGuard
    (Current.globalSmoothRegularityProved
      Current.canonicalClayNSCurrentStateReceipt)
    refl
    (Gap.bkmVorticityControlClosed
      (Current.regularityGapReceipt
        Current.canonicalClayNSCurrentStateReceipt))
    refl
    (Current.clayNavierStokesPromoted
      Current.canonicalClayNSCurrentStateReceipt)
    refl
    true
    refl
    false
    refl

canonicalNSPromotionGuard : Bool
canonicalNSPromotionGuard =
  promotionGuard canonicalNSAuthorityConsistencyGuard

canonicalNSPromotionGuardIsFalse :
  canonicalNSPromotionGuard ≡ false
canonicalNSPromotionGuardIsFalse =
  promotionGuardIsFalse canonicalNSAuthorityConsistencyGuard
