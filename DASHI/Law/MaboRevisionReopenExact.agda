module DASHI.Law.MaboRevisionReopenExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Empty using (⊥)

import DASHI.Law.GenericReviewedDeltaCampaignKernelExact as Kernel
import DASHI.Law.MaboGenericLegalFollowAdapterExact as Mabo
import DASHI.Law.LegalWorldRevisionReconstructionExact as World

------------------------------------------------------------------------
-- S16.8 / S18.6-S18.8.
--
-- A changed reviewed Wikidata manifestation reopens the exact source/context
-- observation that depended on it.  It does not directly invalidate or invent
-- a SameObject identity conclusion.  Only after exact R1 acquisition and
-- explicit bounded-context review may the Mabo consumer be recomputed; any
-- newly exposed identity residual then enters the same generic reviewed-delta
-- kernel as every other domain.
------------------------------------------------------------------------

data RevisionStage : Set where
  reviewedR0 : RevisionStage
  revisionChangedR1 : RevisionStage
  contextReviewRequiredR1 : RevisionStage
  contextReviewedR1 : RevisionStage
  identityResidualExposed : RevisionStage
  identityReviewed : RevisionStage
  frontierClosedAgain : RevisionStage

data ReopenKind : Set where
  reopenContextSource : ReopenKind
  reopenIdentity : ReopenKind

revisionChangeFirstReopens : RevisionStage → ReopenKind
revisionChangeFirstReopens reviewedR0 = reopenContextSource
revisionChangeFirstReopens revisionChangedR1 = reopenContextSource
revisionChangeFirstReopens contextReviewRequiredR1 = reopenContextSource
revisionChangeFirstReopens contextReviewedR1 = reopenContextSource
revisionChangeFirstReopens identityResidualExposed = reopenIdentity
revisionChangeFirstReopens identityReviewed = reopenIdentity
revisionChangeFirstReopens frontierClosedAgain = reopenContextSource

revisionChangeDoesNotDirectlyReopenIdentity :
  revisionChangeFirstReopens revisionChangedR1 ≡ reopenContextSource
revisionChangeDoesNotDirectlyReopenIdentity = refl

data FailedRevisionLookupAutomaticallyUnchanged : Set where
data TruncatedRevisionProbeAutomaticallyClosed : Set where

failedLookupCannotBecomeUnchanged :
  FailedRevisionLookupAutomaticallyUnchanged → ⊥
failedLookupCannotBecomeUnchanged ()

truncatedProbeCannotBecomeClosed :
  TruncatedRevisionProbeAutomaticallyClosed → ⊥
truncatedProbeCannotBecomeClosed ()

data RevisionChangedAutomaticallyIdentityDelta : Set where
data NewManifestationAutomaticallyReviewed : Set where
data RecomputedIdentityResidualAutomaticallyReviewed : Set where

revisionChangeCannotCreateIdentityDelta :
  RevisionChangedAutomaticallyIdentityDelta → ⊥
revisionChangeCannotCreateIdentityDelta ()

newManifestationCannotReviewItself :
  NewManifestationAutomaticallyReviewed → ⊥
newManifestationCannotReviewItself ()

freshIdentityResidualCannotReviewItself :
  RecomputedIdentityResidualAutomaticallyReviewed → ⊥
freshIdentityResidualCannotReviewItself ()

------------------------------------------------------------------------
-- Reviewed/recomputed identity work reuses the already-formalised generic
-- campaign kernel rather than defining a Mabo-only recurrence.
------------------------------------------------------------------------

genericKernelBoundary :
  Kernel.GenericReviewedDeltaCampaignKernelBoundary
genericKernelBoundary =
  Kernel.canonicalGenericReviewedDeltaCampaignKernelBoundary

maboAdapterBoundary :
  Mabo.MaboGenericLegalFollowAdapterBoundary
maboAdapterBoundary =
  Mabo.canonicalMaboGenericLegalFollowAdapterBoundary

worldRevisionBoundary :
  World.LegalWorldRevisionReconstructionBoundary
worldRevisionBoundary =
  World.canonicalLegalWorldRevisionReconstructionBoundary

record MaboRevisionReopenBoundary : Set where
  constructor maboRevisionReopenBoundary
  field
    revisionChangeReopensContextBeforeIdentity : Bool
    revisionChangeReopensContextBeforeIdentityIsTrue :
      revisionChangeReopensContextBeforeIdentity ≡ true

    latestRevisionLookupPaysContextReview : Bool
    latestRevisionLookupPaysContextReviewIsFalse :
      latestRevisionLookupPaysContextReview ≡ false

    latestRevisionLookupFailureMayCountAsUnchanged : Bool
    latestRevisionLookupFailureMayCountAsUnchangedIsFalse :
      latestRevisionLookupFailureMayCountAsUnchanged ≡ false

    truncatedRevisionProbeMayCloseFrontier : Bool
    truncatedRevisionProbeMayCloseFrontierIsFalse :
      truncatedRevisionProbeMayCloseFrontier ≡ false

    exactR1AcquisitionPaysContextReview : Bool
    exactR1AcquisitionPaysContextReviewIsFalse :
      exactR1AcquisitionPaysContextReview ≡ false

    explicitR1ContextReviewMayTriggerRecomputation : Bool
    explicitR1ContextReviewMayTriggerRecomputationIsTrue :
      explicitR1ContextReviewMayTriggerRecomputation ≡ true

    recomputationMayExposeFreshIdentityResidual : Bool
    recomputationMayExposeFreshIdentityResidualIsTrue :
      recomputationMayExposeFreshIdentityResidual ≡ true

    freshIdentityResidualRequiresReviewedDelta : Bool
    freshIdentityResidualRequiresReviewedDeltaIsTrue :
      freshIdentityResidualRequiresReviewedDelta ≡ true

    reviewedIdentityDeltaUsesGenericKernel : Bool
    reviewedIdentityDeltaUsesGenericKernelIsTrue :
      reviewedIdentityDeltaUsesGenericKernel ≡ true

    revisionReopenCreatesSemanticAuthority : Bool
    revisionReopenCreatesSemanticAuthorityIsFalse :
      revisionReopenCreatesSemanticAuthority ≡ false

    revisionReopenCreatesClaimTruth : Bool
    revisionReopenCreatesClaimTruthIsFalse :
      revisionReopenCreatesClaimTruth ≡ false

open MaboRevisionReopenBoundary public

canonicalMaboRevisionReopenBoundary :
  MaboRevisionReopenBoundary
canonicalMaboRevisionReopenBoundary =
  maboRevisionReopenBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    true refl
    false refl
    false refl