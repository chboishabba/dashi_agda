module DASHI.Governance.ArchiveGenocideGeolocationAntiTargetingExact where

open import DASHI.Core.Prelude

import DASHI.Core.AttributedSourceCore as Attribution
import DASHI.Core.ConsumerDescentMinimalObserverExact as Consumer
import DASHI.Interop.GodsEyeViewProofCarryingWorldOntologyExact as Anti

------------------------------------------------------------------------
-- ARCHIVE GENOCIDE GEOLOCATION x DASHI COARSE/FINE EVIDENCE DISCLOSURE
--
-- Public-system inspiration / evidence-method source:
--   Archive Genocide, Geolocation Map / Gaza Node Map
--   https://archivegenocide.com/geolocation
--   https://archivegenocide.com/nodes/
--   inspected 2026-10-16.
--
-- The public methodology distinguishes coarse and fine geolocation, review and
-- conflict states, event-date evidence from post timestamps, independently
-- produced third-party geolocation, and provenance-bearing event links.  The
-- node-map methodology states that coordinates are not model-produced and that
-- stronger event merges are based on reproducible signals while weaker links
-- remain explicitly possible/unconfirmed.
--
-- IMPORTANT ATTRIBUTION BOUNDARY
--
-- Archive Genocide owns its published interface and methodology statements.
-- The dependent types, consumer-descent proof, minimum-sufficient-observer
-- interpretation, anti-targeting release kernel, and all safety theorems below
-- are DASHI constructions.  They are not attributed to Archive Genocide.
--
-- This module deliberately contains no operational geolocation algorithm,
-- coordinate solver, target-selection rule, identity-resolution procedure, or
-- weapon-employment path.  It formalises retrospective evidentiary disclosure
-- and proves that operational targeting is not an admissible evidence consumer.
------------------------------------------------------------------------

archiveGenocideGeolocationSource : Attribution.AttributedSource
archiveGenocideGeolocationSource = Attribution.mkNoDOISource
  "Archive Genocide"
  "Geolocation Map and Gaza Node Map methodology"
  "archivegenocide.com"
  "2026"
  "https://archivegenocide.com/geolocation"
  (Attribution.namedSourceKind "public evidentiary archive methodology")
  "Owns the observed public methodology only: provenance-bearing geolocation, review/conflict distinctions, temporal-source distinctions and event-link calibration. DASHI owns the formal consumer-descent and anti-targeting construction."
  Attribution.publicAttribution

archiveGenocideNodeMapSource : Attribution.AttributedSource
archiveGenocideNodeMapSource = Attribution.mkNoDOISource
  "Archive Genocide"
  "Gaza Node Map"
  "archivegenocide.com"
  "2026"
  "https://archivegenocide.com/nodes/"
  (Attribution.namedSourceKind "public evidentiary archive methodology")
  "Owns the public statement that coordinates are source-checkable rather than model-produced, event merges use reproducible signals, and weaker links remain possible/unconfirmed rather than silently promoted."
  Attribution.publicAttribution

------------------------------------------------------------------------
-- 1. Evidence coordinates.  Precision, review, time basis and origin are
-- independent coordinates: none silently promotes another.
------------------------------------------------------------------------

data LocationPrecision : Set where
  townOrCity : LocationPrecision
  neighbourhoodOrCamp : LocationPrecision
  buildingOrFacility : LocationPrecision
  exactCoordinate : LocationPrecision

data GeolocationReviewState : Set where
  awaitingReview : GeolocationReviewState
  reviewed : GeolocationReviewState
  conflictingSources : GeolocationReviewState
  suggestionUnderReview : GeolocationReviewState

data EventTimeBasis : Set where
  dateStatedInCaption : EventTimeBasis
  dateFromIndependentRecord : EventTimeBasis
  uploadTimestampOnly : EventTimeBasis
  eventTimeUnresolved : EventTimeBasis

data GeolocationOrigin : Set where
  archiveResolved : GeolocationOrigin
  independentThirdPartyOSINT : GeolocationOrigin
  userSubmittedSuggestion : GeolocationOrigin

data SubjectProtection : Set where
  protectedPerson : SubjectProtection
  publicFacility : SubjectProtection
  genericPlace : SubjectProtection

data TemporalClass : Set where
  retrospective : TemporalClass
  delayed : TemporalClass
  nearRealTime : TemporalClass

------------------------------------------------------------------------
-- 2. Bounded coarse/fine witness.
--
-- These constructors are abstract proof tokens, not published coordinates.
-- siteA and siteB witness the important shape: two rival fine claims may remain
-- genuinely distinct while agreeing after coarse projection.
------------------------------------------------------------------------

data CoarsePlace : Set where
  sharedNeighbourhood : CoarsePlace
  otherNeighbourhood : CoarsePlace

data FinePlace : Set where
  siteA : FinePlace
  siteB : FinePlace
  otherSite : FinePlace

coarsen : FinePlace → CoarsePlace
coarsen siteA = sharedNeighbourhood
coarsen siteB = sharedNeighbourhood
coarsen otherSite = otherNeighbourhood

rivalFineClaimsAgreeCoarsely : coarsen siteA ≡ coarsen siteB
rivalFineClaimsAgreeCoarsely = refl

rivalFineClaimsRemainDistinct : siteA ≡ siteB → ⊥
rivalFineClaimsRemainDistinct ()

------------------------------------------------------------------------
-- 3. Geolocation evidence object.
------------------------------------------------------------------------

record GeolocationEvidence : Set where
  constructor geolocation-evidence
  field
    mediaReference : String
    eventReference : String
    finePlace : FinePlace
    statedPrecision : LocationPrecision
    reviewState : GeolocationReviewState
    eventTimeBasis : EventTimeBasis
    origin : GeolocationOrigin
    provenanceReference : String
    corroborationReference : String
    subjectProtection : SubjectProtection
    temporalClass : TemporalClass

open GeolocationEvidence public

coarseEvidencePlace : GeolocationEvidence → CoarsePlace
coarseEvidencePlace evidence = coarsen (finePlace evidence)

------------------------------------------------------------------------
-- 4. Literal consumer descent.
--
-- The coarse observer is sufficient for a consumer that needs only the coarse
-- place, and the canonical coarse consumer is least sufficient in the existing
-- DASHI information order.  The same coarse observer is NOT sufficient for a
-- consumer that requires the fine state: siteA/siteB are the explicit
-- non-descent witness.
------------------------------------------------------------------------

coarseConsumer : FinePlace → CoarsePlace
coarseConsumer = coarsen

fineConsumer : FinePlace → FinePlace
fineConsumer place = place

coarseObserverIsConsumerSufficient :
  Consumer.ConsumerSufficient coarsen coarseConsumer
coarseObserverIsConsumerSufficient =
  Consumer.consumerObserverIsSufficient coarseConsumer

coarseObserverIsLeastSufficient :
  Consumer.LeastSufficientConsumerObserver coarseConsumer
coarseObserverIsLeastSufficient =
  Consumer.canonicalConsumerObserverIsLeast coarseConsumer

fineConsumerNonDescentWitness :
  Consumer.ConsumerNonDescentWitness coarsen fineConsumer
fineConsumerNonDescentWitness =
  Consumer.consumerNonDescentWitness
    siteA
    siteB
    rivalFineClaimsAgreeCoarsely
    rivalFineClaimsRemainDistinct

coarseObserverCannotServeFineConsumer :
  Consumer.ConsumerSufficient coarsen fineConsumer → ⊥
coarseObserverCannotServeFineConsumer =
  Consumer.nonDescentWitnessBlocksSufficiency fineConsumerNonDescentWitness

coarseObserverCannotFactorFineConsumer :
  Consumer.FactorsThrough coarsen fineConsumer → ⊥
coarseObserverCannotFactorFineConsumer =
  Consumer.nonDescentWitnessBlocksFactorization fineConsumerNonDescentWitness

------------------------------------------------------------------------
-- 5. Consumer/purpose firewall.
--
-- There is intentionally no EvidenceConsumer constructor for operational
-- targeting.  A consumer may be epistemically interested in a fine state and
-- still lack disclosure authority; information sufficiency and authority are
-- separate coordinates.
------------------------------------------------------------------------

data GeolocationConsumer : Set where
  historicalArchiveConsumer : GeolocationConsumer
  legalAccountabilityConsumer : GeolocationConsumer
  evidentiaryResearchConsumer : GeolocationConsumer
  publicPresentationConsumer : GeolocationConsumer
  operationalTargetingConsumer : GeolocationConsumer

data EvidenceConsumer : GeolocationConsumer → Set where
  historicalArchiveEvidence : EvidenceConsumer historicalArchiveConsumer
  legalAccountabilityEvidence : EvidenceConsumer legalAccountabilityConsumer
  evidentiaryResearchEvidence : EvidenceConsumer evidentiaryResearchConsumer
  publicPresentationEvidence : EvidenceConsumer publicPresentationConsumer

operationalTargetingConsumerIsNotEvidenceConsumer :
  EvidenceConsumer operationalTargetingConsumer → ⊥
operationalTargetingConsumerIsNotEvidenceConsumer ()

------------------------------------------------------------------------
-- 6. Temporal and protected-subject disclosure kernel.
------------------------------------------------------------------------

data SafeTemporal : TemporalClass → Set where
  retrospectiveSafe : SafeTemporal retrospective
  delayedSafe : SafeTemporal delayed

nearRealTimeIsNotSafeTemporal : SafeTemporal nearRealTime → ⊥
nearRealTimeIsNotSafeTemporal ()

data ProtectedPrecisionSafe : SubjectProtection → LocationPrecision → Set where
  protectedTownSafe : ProtectedPrecisionSafe protectedPerson townOrCity
  protectedNeighbourhoodSafe :
    ProtectedPrecisionSafe protectedPerson neighbourhoodOrCamp
  publicFacilityPrecisionSafe :
    ∀ {precision} → ProtectedPrecisionSafe publicFacility precision
  genericPlacePrecisionSafe :
    ∀ {precision} → ProtectedPrecisionSafe genericPlace precision

protectedExactPrecisionIsNotSafe :
  ProtectedPrecisionSafe protectedPerson exactCoordinate → ⊥
protectedExactPrecisionIsNotSafe ()

protectedBuildingPrecisionIsNotSafe :
  ProtectedPrecisionSafe protectedPerson buildingOrFacility → ⊥
protectedBuildingPrecisionIsNotSafe ()

record SafeDisclosureReceipt
    (evidence : GeolocationEvidence)
    (consumer : GeolocationConsumer)
    (disclosedPrecision : LocationPrecision) : Set where
  constructor safe-disclosure-receipt
  field
    evidenceConsumer : EvidenceConsumer consumer
    reviewComplete : reviewState evidence ≡ reviewed
    safeTemporal : SafeTemporal (temporalClass evidence)
    protectedPrecisionSafe :
      ProtectedPrecisionSafe (subjectProtection evidence) disclosedPrecision
    provenanceRetained : Bool
    provenanceRetainedIsTrue : provenanceRetained ≡ true
    conflictStateNotSilentlyErased : Bool
    conflictStateNotSilentlyErasedIsTrue : conflictStateNotSilentlyErased ≡ true
    thirdPartyOriginNotReattributed : Bool
    thirdPartyOriginNotReattributedIsTrue : thirdPartyOriginNotReattributed ≡ true

open SafeDisclosureReceipt public

operationalTargetingReleaseImpossible :
  ∀ {evidence precision} →
  SafeDisclosureReceipt evidence operationalTargetingConsumer precision → ⊥
operationalTargetingReleaseImpossible receipt =
  operationalTargetingConsumerIsNotEvidenceConsumer (evidenceConsumer receipt)

protectedExactReleaseImpossible :
  ∀ {evidence consumer} →
  subjectProtection evidence ≡ protectedPerson →
  SafeDisclosureReceipt evidence consumer exactCoordinate → ⊥
protectedExactReleaseImpossible refl receipt =
  protectedExactPrecisionIsNotSafe (protectedPrecisionSafe receipt)

nearRealTimeReleaseImpossible :
  ∀ {evidence consumer precision} →
  temporalClass evidence ≡ nearRealTime →
  SafeDisclosureReceipt evidence consumer precision → ⊥
nearRealTimeReleaseImpossible refl receipt =
  nearRealTimeIsNotSafeTemporal (safeTemporal receipt)

protectedNearRealTimeExactReleaseImpossible :
  ∀ {evidence consumer} →
  subjectProtection evidence ≡ protectedPerson →
  temporalClass evidence ≡ nearRealTime →
  SafeDisclosureReceipt evidence consumer exactCoordinate → ⊥
protectedNearRealTimeExactReleaseImpossible protectedIsPerson nearRealTimeIsLive receipt =
  nearRealTimeReleaseImpossible nearRealTimeIsLive receipt

------------------------------------------------------------------------
-- 7. Promotion firewalls.
------------------------------------------------------------------------

data ReviewCreatesExactLocation : Set where

reviewDoesNotCreateExactness : ReviewCreatesExactLocation → ⊥
reviewDoesNotCreateExactness ()

data ThirdPartyGeolocationCreatesArchiveAuthorship : Set where

thirdPartyGeolocationDoesNotCreateArchiveAuthorship :
  ThirdPartyGeolocationCreatesArchiveAuthorship → ⊥
thirdPartyGeolocationDoesNotCreateArchiveAuthorship ()

data ConflictMayBeSilentlyCollapsed : Set where

conflictMayNotBeSilentlyCollapsed : ConflictMayBeSilentlyCollapsed → ⊥
conflictMayNotBeSilentlyCollapsed ()

------------------------------------------------------------------------
-- 8. Imported same-object anchors.
------------------------------------------------------------------------

antiPanopticonBoundaryAnchor : Anti.AntiPanopticonBoundary
antiPanopticonBoundaryAnchor = Anti.canonicalAntiPanopticonBoundary

consumerDescentBoundaryAnchor : Consumer.ConsumerDescentMinimalObserverBoundary
consumerDescentBoundaryAnchor =
  Consumer.canonicalConsumerDescentMinimalObserverBoundary

------------------------------------------------------------------------
-- 9. Terminal max-cut boundary.
------------------------------------------------------------------------

record ArchiveGenocideGeolocationMaxCutBoundary : Set where
  constructor archive-genocide-geolocation-max-cut-boundary
  field
    coarseFineClaimsRemainDistinct : Bool
    coarseFineClaimsRemainDistinctIsTrue : coarseFineClaimsRemainDistinct ≡ true

    rivalFineClaimsMayAgreeAfterCoarsening : Bool
    rivalFineClaimsMayAgreeAfterCoarseningIsTrue :
      rivalFineClaimsMayAgreeAfterCoarsening ≡ true

    coarseObservationServesCoarseConsumer : Bool
    coarseObservationServesCoarseConsumerIsTrue :
      coarseObservationServesCoarseConsumer ≡ true

    coarseObservationServesEveryFineConsumer : Bool
    coarseObservationServesEveryFineConsumerIsFalse :
      coarseObservationServesEveryFineConsumer ≡ false

    minimumSufficientObserverRequired : Bool
    minimumSufficientObserverRequiredIsTrue :
      minimumSufficientObserverRequired ≡ true

    provenanceMustSurviveDisclosure : Bool
    provenanceMustSurviveDisclosureIsTrue :
      provenanceMustSurviveDisclosure ≡ true

    conflictMustRemainVisible : Bool
    conflictMustRemainVisibleIsTrue : conflictMustRemainVisible ≡ true

    reviewCreatesGeometricExactness : Bool
    reviewCreatesGeometricExactnessIsFalse :
      reviewCreatesGeometricExactness ≡ false

    thirdPartyCreditMustRemainDistinct : Bool
    thirdPartyCreditMustRemainDistinctIsTrue :
      thirdPartyCreditMustRemainDistinct ≡ true

    evidentiaryGeolocationEqualsOperationalGeolocation : Bool
    evidentiaryGeolocationEqualsOperationalGeolocationIsFalse :
      evidentiaryGeolocationEqualsOperationalGeolocation ≡ false

    operationalTargetingIsEvidenceConsumer : Bool
    operationalTargetingIsEvidenceConsumerIsFalse :
      operationalTargetingIsEvidenceConsumer ≡ false

    protectedFineNearRealTimeDisclosureAllowed : Bool
    protectedFineNearRealTimeDisclosureAllowedIsFalse :
      protectedFineNearRealTimeDisclosureAllowed ≡ false

    archiveMethodologyOwnsDASHITheorems : Bool
    archiveMethodologyOwnsDASHITheoremsIsFalse :
      archiveMethodologyOwnsDASHITheorems ≡ false

open ArchiveGenocideGeolocationMaxCutBoundary public

archiveGenocideGeolocationMaxCutBoundary : ArchiveGenocideGeolocationMaxCutBoundary
archiveGenocideGeolocationMaxCutBoundary =
  archive-genocide-geolocation-max-cut-boundary
    true refl
    true refl
    true refl
    false refl
    true refl
    true refl
    true refl
    false refl
    true refl
    false refl
    false refl
    false refl
    false refl
