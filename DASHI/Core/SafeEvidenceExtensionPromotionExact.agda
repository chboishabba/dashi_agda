module DASHI.Core.SafeEvidenceExtensionPromotionExact where

------------------------------------------------------------------------
-- More data is not automatically more authority.  Promotion may be monotone
-- only along a declared claim-specific support order, under unchanged relevant
-- assumptions and with no newly introduced contradiction.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; true)

record ClaimEvidenceOrder
    (Claim Evidence : Set) : Set₁ where
  constructor claimEvidenceOrder
  field
    SupportsAtLeast : Claim → Evidence → Evidence → Set
    NoNewContradiction : Claim → Evidence → Evidence → Set
    RelevantAssumptionsStable : Claim → Evidence → Evidence → Set

open ClaimEvidenceOrder public

record SafeEvidenceExtension
    {Claim Evidence : Set}
    (order : ClaimEvidenceOrder Claim Evidence)
    (claim : Claim)
    (before after : Evidence) : Set where
  constructor safeEvidenceExtension
  field
    supportMonotone : SupportsAtLeast order claim before after
    noNewContradiction : NoNewContradiction order claim before after
    assumptionsStable : RelevantAssumptionsStable order claim before after

open SafeEvidenceExtension public

record PromotionPolicy
    {Claim Evidence : Set}
    (order : ClaimEvidenceOrder Claim Evidence) : Set₁ where
  constructor promotionPolicy
  field
    Promoted : Claim → Evidence → Set
    safeExtensionPreservesPromotion :
      ∀ claim before after →
      SafeEvidenceExtension order claim before after →
      Promoted claim before →
      Promoted claim after

open PromotionPolicy public

promotionPersistsUnderSafeEvidenceExtension :
  ∀ {Claim Evidence}
    {order : ClaimEvidenceOrder Claim Evidence}
    (policy : PromotionPolicy order)
    {claim before after} →
  SafeEvidenceExtension order claim before after →
  Promoted policy claim before →
  Promoted policy claim after
promotionPersistsUnderSafeEvidenceExtension policy extension promoted =
  safeExtensionPreservesPromotion policy _ _ _ extension promoted

record SafeEvidencePromotionBoundary : Set where
  constructor safeEvidencePromotionBoundary
  field
    arbitraryMoreEvidenceNeedNotIncreaseAuthority : Bool
    supportOrderIsClaimSpecific : Bool
    contradictionCanForceReopening : Bool
    assumptionChangeCanForceReopening : Bool
    monotonicityRequiresSafeExtensionWitness : Bool

canonicalSafeEvidencePromotionBoundary : SafeEvidencePromotionBoundary
canonicalSafeEvidencePromotionBoundary =
  safeEvidencePromotionBoundary true true true true true
