module DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingValidation where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingExact as G
import DASHI.Governance.ArchiveGenocideGeolocationPrecisionDisclosureExact as P

rivalFineAgreementValidated : G.coarsen G.siteA ≡ G.coarsen G.siteB
rivalFineAgreementValidated = G.rivalFineClaimsAgreeCoarsely

rivalFineDistinctnessValidated : G.siteA ≡ G.siteB → ⊥
rivalFineDistinctnessValidated = G.rivalFineClaimsRemainDistinct

coarseConsumerSufficiencyValidated :
  Consumer.ConsumerSufficient G.coarsen G.coarseConsumer
coarseConsumerSufficiencyValidated = G.coarseObserverIsConsumerSufficient

fineConsumerNonDescentValidated :
  Consumer.ConsumerSufficient G.coarsen G.fineConsumer → ⊥
fineConsumerNonDescentValidated = G.coarseObserverCannotServeFineConsumer

targetingConsumerBlockedValidated :
  G.EvidenceConsumer G.operationalTargetingConsumer → ⊥
targetingConsumerBlockedValidated =
  G.operationalTargetingConsumerIsNotEvidenceConsumer

protectedLiveExactBlockedValidated :
  ∀ {evidence consumer} →
  G.subjectProtection evidence ≡ G.protectedPerson →
  G.temporalClass evidence ≡ G.nearRealTime →
  G.SafeDisclosureReceipt evidence consumer G.exactCoordinate → ⊥
protectedLiveExactBlockedValidated =
  G.protectedNearRealTimeExactReleaseImpossible

provenanceRetentionValidated :
  G.provenanceMustSurviveDisclosure G.archiveGenocideGeolocationMaxCutBoundary ≡ true
provenanceRetentionValidated =
  G.provenanceMustSurviveDisclosureIsTrue
    G.archiveGenocideGeolocationMaxCutBoundary

conflictVisibilityValidated :
  G.conflictMustRemainVisible G.archiveGenocideGeolocationMaxCutBoundary ≡ true
conflictVisibilityValidated =
  G.conflictMustRemainVisibleIsTrue
    G.archiveGenocideGeolocationMaxCutBoundary

antiTargetingBoundaryValidated :
  G.operationalTargetingIsEvidenceConsumer
    G.archiveGenocideGeolocationMaxCutBoundary
  ≡ false
antiTargetingBoundaryValidated =
  G.operationalTargetingIsEvidenceConsumerIsFalse
    G.archiveGenocideGeolocationMaxCutBoundary

precisionTransitivityValidated :
  P.PrecisionRefines G.exactCoordinate G.townOrCity
precisionTransitivityValidated =
  P.precisionRefinesTrans
    P.exactRefinesBuilding
    P.buildingRefinesTown

reviewDoesNotDeterminePrecisionValidated :
  proj₁ P.reviewedExact ≡ proj₁ P.reviewedTown
reviewDoesNotDeterminePrecisionValidated = P.sameReviewDifferentPrecision

reviewedPrecisionsRemainDistinctValidated :
  proj₂ P.reviewedExact ≡ proj₂ P.reviewedTown → ⊥
reviewedPrecisionsRemainDistinctValidated =
  P.reviewedExactPrecisionDiffersFromReviewedTown

thirdPartyCreditSeparationValidated :
  proj₁ P.thirdPartyReviewed ≡ proj₁ P.archiveReviewed → ⊥
thirdPartyCreditSeparationValidated = P.thirdPartyOriginRemainsDistinct

minimumDisclosurePreservesProvenanceValidated :
  ∀ (evidence : G.GeolocationEvidence)
    (refinement :
      P.PrecisionRefines
        (G.statedPrecision evidence)
        G.neighbourhoodOrCamp) →
  P.provenanceReference (P.minimumNeighbourhoodDisclosure evidence refinement)
    ≡ G.provenanceReference evidence
minimumDisclosurePreservesProvenanceValidated =
  P.provenanceSurvivesMinimumDisclosure
