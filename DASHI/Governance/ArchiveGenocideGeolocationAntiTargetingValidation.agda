module DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingValidation where

open import DASHI.Core.Prelude

import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingExact as G

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
