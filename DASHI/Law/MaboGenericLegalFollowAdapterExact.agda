module DASHI.Law.MaboGenericLegalFollowAdapterExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.GenericReviewedDeltaCampaignKernelExact as Kernel
import DASHI.Interop.SensibLawMaboProgressiveExplanationProjectionExact as Mabo

------------------------------------------------------------------------
-- S16: Mabo/public-law is a genuinely distinct legal domain adapter over the
-- same reviewed-delta recurrence.  The generic kernel is reused; Mabo source,
-- identity, review and persistence semantics remain domain-owned.
------------------------------------------------------------------------

genericKernelBoundary :
  Kernel.GenericReviewedDeltaCampaignKernelBoundary
genericKernelBoundary =
  Kernel.canonicalGenericReviewedDeltaCampaignKernelBoundary

maboProjectionBoundary :
  Mabo.MaboThinProfileBoundary
maboProjectionBoundary =
  Mabo.canonicalMaboThinProfileBoundary

record MaboGenericLegalFollowAdapterBoundary : Set where
  constructor maboGenericLegalFollowAdapterBoundary
  field
    maboUsesGenericReviewedDeltaKernel : Bool
    maboUsesGenericReviewedDeltaKernelIsTrue :
      maboUsesGenericReviewedDeltaKernel ≡ true

    maboRequiresContractDoctrine : Bool
    maboRequiresContractDoctrineIsFalse :
      maboRequiresContractDoctrine ≡ false

    maboRawSourceMayBecomeReviewedDelta : Bool
    maboRawSourceMayBecomeReviewedDeltaIsFalse :
      maboRawSourceMayBecomeReviewedDelta ≡ false

    missingMaboIdentityReviewMayBeFabricated : Bool
    missingMaboIdentityReviewMayBeFabricatedIsFalse :
      missingMaboIdentityReviewMayBeFabricated ≡ false

    maboProjectionCreatesLegalAuthority : Bool
    maboProjectionCreatesLegalAuthorityIsFalse :
      maboProjectionCreatesLegalAuthority ≡ false

    genericMaboAdapterPromotesClaimTruth : Bool
    genericMaboAdapterPromotesClaimTruthIsFalse :
      genericMaboAdapterPromotesClaimTruth ≡ false

open MaboGenericLegalFollowAdapterBoundary public

canonicalMaboGenericLegalFollowAdapterBoundary :
  MaboGenericLegalFollowAdapterBoundary
canonicalMaboGenericLegalFollowAdapterBoundary =
  maboGenericLegalFollowAdapterBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    false refl

data MissingMaboReviewAutomaticallyDelta : Set where
data GenericKernelAutomaticallyContractDoctrine : Set where

missingMaboReviewCannotBecomeDelta :
  MissingMaboReviewAutomaticallyDelta → ⊥
missingMaboReviewCannotBecomeDelta ()

genericKernelDoesNotForceContractDoctrine :
  GenericKernelAutomaticallyContractDoctrine → ⊥
genericKernelDoesNotForceContractDoctrine ()