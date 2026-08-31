module DASHI.Culture.JohnAnthonyBrownRetrospectiveExposureProvenanceExact where

------------------------------------------------------------------------
-- JOHN ANTHONY BROWN: RETROSPECTIVE EXPOSURE PROVENANCE
--
-- Authorial programme source: John Anthony Brown.
--
-- The current proposal is prospective with respect to adult follow-up but
-- retrospective with respect to childhood exposure.  This owner keeps those
-- time/provenance layers distinct.  It is structurally cross-pollinated from
-- repository provenance/governance work, without importing an unmerged branch.
------------------------------------------------------------------------

open import DASHI.Core.Prelude
open import Agda.Builtin.String using (String)

data ObservationTime : Set where
  childhoodContemporaneous : ObservationTime
  adultBaselineRecall : ObservationTime
  adultFollowup : ObservationTime

data ProvenanceClass : Set where
  contemporaneousRecord : ProvenanceClass
  retrospectiveFirstPersonReport : ProvenanceClass
  parentOrAuthorityRecord : ProvenanceClass
  institutionalArchive : ProvenanceClass
  laterInterpretation : ProvenanceClass

data EpistemicStatus : Set where
  directlyObserved : EpistemicStatus
  participantRecalled : EpistemicStatus
  corroborated : EpistemicStatus
  disputed : EpistemicStatus
  unresolved : EpistemicStatus

record ExposureObservation : Set where
  constructor exposure-observation
  field
    proposition : String
    observedAt : ObservationTime
    provenance : ProvenanceClass
    status : EpistemicStatus
    sourceRole : String

open ExposureObservation public

adultRecallOfChildhoodThreat : ExposureObservation
adultRecallOfChildhoodThreat = exposure-observation
  "participant reports childhood exposure to divine-sanction / hell threat"
  adultBaselineRecall retrospectiveFirstPersonReport participantRecalled
  "first-person evidence about remembered childhood experience; not identical to a contemporaneous childhood record and not null merely because it is retrospective"

contemporaneousChildDiaryExample : ExposureObservation
contemporaneousChildDiaryExample = exposure-observation
  "religious parent-child communication recorded during childhood"
  childhoodContemporaneous contemporaneousRecord directlyObserved
  "contemporaneous communication evidence can recover interaction structure but need not recover the child's latent fear, autonomy or later interpretation"

record ProvenanceWeld : Set where
  constructor provenance-weld
  field
    childhoodEventClaim : String
    presentReport : ExposureObservation
    corroboratingRecordPresent : Bool
    contradictionPresent : Bool
    safeReading : String

canonicalRetrospectiveWeld : ProvenanceWeld
canonicalRetrospectiveWeld = provenance-weld
  "childhood religious exposure occurred with the reported features"
  adultRecallOfChildhoodThreat
  false false
  "retain the adult retrospective report as participant evidence while keeping contemporaneous corroboration and contradiction as independent coordinates"

------------------------------------------------------------------------
-- BIDI boundaries.
------------------------------------------------------------------------

data RetrospectiveReportPromotesContemporaneousRecord : Set where

data NoContemporaneousRecordPromotesFalseRecall : Set where

data ContemporaneousInteractionPromotesLatentFear : Set where

data CorroborationPromotesUniqueInterpretation : Set where

data AdultMeaningPromotesChildhoodMeaningIdentity : Set where

retrospectiveReportDoesNotPromoteContemporaneousRecord :
  RetrospectiveReportPromotesContemporaneousRecord -> ⊥
retrospectiveReportDoesNotPromoteContemporaneousRecord ()

absenceOfContemporaneousRecordDoesNotPromoteFalseRecall :
  NoContemporaneousRecordPromotesFalseRecall -> ⊥
absenceOfContemporaneousRecordDoesNotPromoteFalseRecall ()

contemporaneousInteractionDoesNotPromoteLatentFear :
  ContemporaneousInteractionPromotesLatentFear -> ⊥
contemporaneousInteractionDoesNotPromoteLatentFear ()

corroborationDoesNotPromoteUniqueInterpretation :
  CorroborationPromotesUniqueInterpretation -> ⊥
corroborationDoesNotPromoteUniqueInterpretation ()

adultMeaningDoesNotPromoteChildhoodMeaningIdentity :
  AdultMeaningPromotesChildhoodMeaningIdentity -> ⊥
adultMeaningDoesNotPromoteChildhoodMeaningIdentity ()

------------------------------------------------------------------------
-- The important design asymmetry: later follow-up can be genuinely prospective
-- for adult outcomes while the childhood exposure coordinate remains recalled.
------------------------------------------------------------------------

record TemporalDesignSplit : Set where
  constructor temporal-design-split
  field
    childhoodExposureMeasuredRetrospectively : Bool
    futureAdultOutcomesMeasuredProspectively : Bool
    prospectiveAdultFollowupMakesChildhoodExposureProspective : Bool
    repeatedAdultFollowupCanImproveOutcomeTemporalResolution : Bool

johnAnthonyBrownTemporalSplit : TemporalDesignSplit
johnAnthonyBrownTemporalSplit = temporal-design-split true true false true

record RetrospectiveExposureBoundary : Set where
  constructor retrospective-exposure-boundary
  field
    authorialProgrammeAttributedToJohnAnthonyBrown : Bool
    retrospectiveReportIsEvidence : Bool
    retrospectiveReportEqualsContemporaneousRecord : Bool
    missingChildhoodRecordRefutesParticipant : Bool
    prospectiveAdultFollowupRepairsExposureProvenance : Bool
    triangulationCanIncreaseConfidence : Bool
    triangulationMakesInterpretationUnique : Bool

canonicalRetrospectiveExposureBoundary : RetrospectiveExposureBoundary
canonicalRetrospectiveExposureBoundary =
  retrospective-exposure-boundary true true false false false true false
