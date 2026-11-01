module DASHI.Physics.Closure.KnownLimitsRecovery where

open import Relation.Binary.PropositionalEquality using (_≡_; refl)

open import DASHI.Physics.Closure.KnownLimitsStatus as KLS

record KnownLimitsRecoveryWitness : Set where
  field
    localLorentzRecovered :
      KLS.KnownLimitsStatus.localLorentz KLS.canonicalKnownLimitsStatus
      ≡ KLS.localLorentzTheoremBacked
    propagationLimitRecovered :
      KLS.KnownLimitsStatus.propagationLimit KLS.canonicalKnownLimitsStatus
      ≡ KLS.propagationLimitSeamBacked
    grLikeRecovered :
      KLS.KnownLimitsStatus.grLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.grLikeTheoremBacked
    qftLikeRecovered :
      KLS.KnownLimitsStatus.qftLike KLS.canonicalKnownLimitsStatus
      ≡ KLS.qftLikeTheoremBacked

canonicalKnownLimitsRecovery : KnownLimitsRecoveryWitness
canonicalKnownLimitsRecovery =
  record
    { localLorentzRecovered = refl
    ; propagationLimitRecovered = refl
    ; grLikeRecovered = refl
    ; qftLikeRecovered = refl
    }
