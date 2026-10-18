module DASHI.Wikimedia.MaboLiveIdentityLineageInteropValidation where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import DASHI.Wikimedia.MaboLiveIdentityLineageInteropExact
import DASHI.Wikimedia.MaboWorldObjectIdentityExact as Identity
import DASHI.Wikimedia.MaboP7d5SlrRuntimeReceiptExact as Runtime

_ : Identity.identityClassReference maboCaseIdentity
    ≡ "world-object:mabo-case-1992-hca-23"
_ = refl

_ : Runtime.identityClassRef Runtime.liveMaboCaseLineage
    ≡ Identity.identityClassReference maboCaseIdentity
_ = refl

_ : Runtime.identityClassRef Runtime.liveEddieMaboLineage
    ≡ Identity.identityClassReference Identity.eddieMaboIdentity
_ = refl

_ : identityClassMatchesGoldenIdentity liveMaboCaseIdentityAttachment ≡ true
_ = refl

_ : identityClassMatchesGoldenIdentity liveEddieMaboIdentityAttachment ≡ true
_ = refl

_ : persistenceObserved liveMaboCaseIdentityAttachment ≡ true
_ = refl

_ : persistenceObserved liveEddieMaboIdentityAttachment ≡ true
_ = refl

_ : persistenceCreatesSemanticAuthority liveMaboCaseIdentityAttachment ≡ false
_ = refl

_ : persistenceCreatesClaimTruth liveEddieMaboIdentityAttachment ≡ false
_ = refl
