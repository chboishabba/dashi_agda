module DASHI.Law.SensibLawMaboDistributedLegalCorpusMaterialisationRegression where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawMaboDistributedLegalCorpusMaterialisationExact as Materialisation

------------------------------------------------------------------------
-- Regression surface for the distributed Mabo legal-corpus materialisation
-- packet.  This file intentionally imported the production owner before that
-- owner existed, giving the tranche its source-level RED state.
------------------------------------------------------------------------

materialisationOrderStartsAtReferenceOnly :
  Materialisation._≺m_
    Materialisation.referenceOnly
    Materialisation.skeletalLegalGraph
materialisationOrderStartsAtReferenceOnly = Materialisation.reference≺skeleton

materialisationOrderEndsAtVerifiedFullSource :
  Materialisation._≺m_
    Materialisation.derivedSpan
    Materialisation.verifiedFullSource
materialisationOrderEndsAtVerifiedFullSource = Materialisation.span≺full

navigationFactorsThroughSkeleton :
  Materialisation.NavigationAdequateThroughSkeleton
navigationFactorsThroughSkeleton = Materialisation.maboNavigationAdequateThroughSkeleton

quotationHasExactSkeletonCollision :
  Materialisation.QuotationSkeletonDefect
quotationHasExactSkeletonCollision = Materialisation.maboQuotationSkeletonDefect

strictPrimaryPaymentHasExactDiscoveryCollision :
  Materialisation.PrimaryPaymentDiscoveryDefect
strictPrimaryPaymentHasExactDiscoveryCollision = Materialisation.maboPrimaryPaymentDiscoveryDefect

maboSpecimenRequiresReacquisition :
  Materialisation.reacquisitionRequired
    Materialisation.canonicalMaboDistributedSpecimen
  ≡ true
maboSpecimenRequiresReacquisition = refl

maboSpecimenRequiresVerifiedSourceSpan :
  Materialisation.verifiedSourceAndExactSpanRequired
    Materialisation.canonicalMaboDistributedSpecimen
  ≡ true
maboSpecimenRequiresVerifiedSourceSpan = refl

maboSpecimenDoesNotAutoPay :
  Materialisation.reacquisitionAutomaticallyPaysResidual
    Materialisation.canonicalMaboDistributedSpecimen
  ≡ false
maboSpecimenDoesNotAutoPay = refl

materialisationDoesNotIncreaseAuthority :
  Materialisation.moreMaterialisedMeansMoreAuthoritative
    Materialisation.canonicalDistributedLegalCorpusBoundary
  ≡ false
materialisationDoesNotIncreaseAuthority = refl

sharedSkeletonIsNotDistributedAuthority :
  Materialisation.sharedPublicSkeletonCreatesDistributedAuthority
    Materialisation.canonicalDistributedLegalCorpusBoundary
  ≡ false
sharedSkeletonIsNotDistributedAuthority = refl
