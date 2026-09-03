module DASHI.Culture.AmyEskridgeEvidenceHyperfabricExact where

------------------------------------------------------------------------
-- AMY ESKRIDGE EVIDENCE HYPERFABRIC
--
-- Case-specific fixture over the generic evidence calculus.  This module does
-- not prove suicide, homicide, directed-energy attack, coercion, or any other
-- contested causal theory.  It records only the evidentiary distinctions
-- needed to investigate the case without flattening primary testimony into a
-- public classification or flattening missing public records into nonexistence.
------------------------------------------------------------------------

open import DASHI.Core.Prelude

import DASHI.Core.EvidenceHyperfabricExact as Evidence
import DASHI.Core.ObserverRefinementLatticeExact as Observer

------------------------------------------------------------------------
-- Case coordinates.
------------------------------------------------------------------------

data EskridgeClaim : Set where
  repeatedResidentialIntrusions
  preDeathThreatConcern
  preDeathFutureSuicideDenial
  publicSuicideClassification
  homicideHypothesis
  suicideHypothesis
  accidentalHypothesis
  undeterminedHypothesis : EskridgeClaim

data EskridgeCaseState : Set where
  publicSurfaceOnly enrichedEvidenceState : EskridgeCaseState

data PublicLabel : Set where
  reportedSuicide : PublicLabel

data ResidualCode : Set where
  noResidualVisible primaryEvidencePresent : ResidualCode

publicLabel : Observer.Observer EskridgeCaseState PublicLabel
publicLabel publicSurfaceOnly = reportedSuicide
publicLabel enrichedEvidenceState = reportedSuicide

residualEvidence : Observer.Observer EskridgeCaseState ResidualCode
residualEvidence publicSurfaceOnly = noResidualVisible
residualEvidence enrichedEvidenceState = primaryEvidencePresent

residualCodesDiffer : noResidualVisible ≡ primaryEvidencePresent → ⊥
residualCodesDiffer ()

samePublicDifferentEvidence :
  Evidence.HiddenCaseEvidence publicLabel residualEvidence
samePublicDifferentEvidence =
  Evidence.hiddenCaseEvidence
    publicSurfaceOnly
    enrichedEvidenceState
    refl
    residualCodesDiffer

publicClassificationStrictlyRefinedByEvidence :
  Observer.StrictRefinement
    publicLabel
    (Observer.pairObserver publicLabel residualEvidence)
publicClassificationStrictlyRefinedByEvidence =
  Evidence.hiddenCaseEvidenceGivesStrictRefinement samePublicDifferentEvidence

publicLabelCannotReconstructEvidence :
  Evidence.ResidualDescendsThroughPublicLabel publicLabel residualEvidence → ⊥
publicLabelCannotReconstructEvidence =
  Evidence.hiddenCaseEvidenceBlocksPublicDescent samePublicDifferentEvidence

------------------------------------------------------------------------
-- Primary testimony receipts.
------------------------------------------------------------------------

record EskridgePrimaryEvidence : Set where
  constructor eskridgePrimaryEvidence
  field
    repeatedIntrusionRecordedPreDeath :
      Evidence.TestimonyFor repeatedResidentialIntrusions
    threatConcernRecordedPreDeath :
      Evidence.TestimonyFor preDeathThreatConcern
    futureSuicideDenialPreDeath :
      Evidence.TestimonyFor preDeathFutureSuicideDenial

open EskridgePrimaryEvidence public

canonicalEskridgePrimaryEvidence : EskridgePrimaryEvidence
canonicalEskridgePrimaryEvidence =
  eskridgePrimaryEvidence
    (Evidence.testimonyFor true refl)
    (Evidence.testimonyFor true refl)
    (Evidence.testimonyFor true refl)

------------------------------------------------------------------------
-- Public-record availability is tri-valued.  Not locating a record is not a
-- proof that no record exists.
------------------------------------------------------------------------

record EskridgeRecordLedger : Set where
  constructor eskridgeRecordLedger
  field
    publicPoliceReport : Evidence.RecordStatus
    publicAutopsy : Evidence.RecordStatus
    publicToxicology : Evidence.RecordStatus
    publicBallisticsOrGSR : Evidence.RecordStatus
    publicApartmentManagementComplaint : Evidence.RecordStatus

open EskridgeRecordLedger public

currentPublicRecordLedger : EskridgeRecordLedger
currentPublicRecordLedger =
  eskridgeRecordLedger
    Evidence.notLocated
    Evidence.notLocated
    Evidence.notLocated
    Evidence.notLocated
    Evidence.notLocated

policeNotLocated≠KnownAbsent :
  publicPoliceReport currentPublicRecordLedger ≡ Evidence.knownAbsent → ⊥
policeNotLocated≠KnownAbsent = Evidence.notLocated≠knownAbsent

autopsyNotLocated≠KnownAbsent :
  publicAutopsy currentPublicRecordLedger ≡ Evidence.knownAbsent → ⊥
autopsyNotLocated≠KnownAbsent = Evidence.notLocated≠knownAbsent

------------------------------------------------------------------------
-- Intrusion-pattern hypotheses remain competitors rather than conclusions.
------------------------------------------------------------------------

data IntrusionHypothesis : Set where
  acquisitiveBurglary
  intimidationOrSignalling
  surveillanceOrSearch
  interpersonalIntrusion
  nonIntrusionExplanation : IntrusionHypothesis

record IntrusionPattern : Set where
  constructor intrusionPattern
  field
    repeatedEventsReported : Bool
    conspicuousDisturbanceReported : Bool
    ordinaryTheftReportedAsCentralFeature : Bool

open IntrusionPattern public

recordedIntrusionPattern : IntrusionPattern
recordedIntrusionPattern = intrusionPattern true true false

record InvestigativeHypothesisSet : Set where
  constructor investigativeHypothesisSet
  field
    acquisitiveOpen : Bool
    intimidationOpen : Bool
    surveillanceOpen : Bool
    interpersonalOpen : Bool
    nonIntrusionOpen : Bool

open InvestigativeHypothesisSet public

intrusionHypothesesRemainOpen : InvestigativeHypothesisSet
intrusionHypothesesRemainOpen =
  investigativeHypothesisSet true true true true true

------------------------------------------------------------------------
-- Death hypotheses are kept explicitly non-collapsed.
------------------------------------------------------------------------

data DeathHypothesis : Set where
  suicide homicide accident undetermined : DeathHypothesis

record EskridgeDeathHypothesisSurface : Set where
  constructor eskridgeDeathHypothesisSurface
  field
    reportedPublicClassification : DeathHypothesis
    publiclyAuditableForensicBasis : Evidence.AuditStatus

open EskridgeDeathHypothesisSurface public

currentDeathHypothesisSurface : EskridgeDeathHypothesisSurface
currentDeathHypothesisSurface =
  eskridgeDeathHypothesisSurface suicide Evidence.notPubliclyAuditable

------------------------------------------------------------------------
-- Family-statement firewall: public acceptance is a statement coordinate, not
-- definitionally a forensic receipt, and it neither proves nor refutes coercion.
------------------------------------------------------------------------

record FamilyStatementBoundary : Set where
  constructor familyStatementBoundary
  field
    publicAcceptanceRecorded : Bool
    publicAcceptanceRecordedIsTrue : publicAcceptanceRecorded ≡ true
    acceptanceIsForensicProof : Bool
    acceptanceIsForensicProofIsFalse : acceptanceIsForensicProof ≡ false
    acceptanceProvesCoercion : Bool
    acceptanceProvesCoercionIsFalse : acceptanceProvesCoercion ≡ false
    acceptanceRefutesCoercion : Bool
    acceptanceRefutesCoercionIsFalse : acceptanceRefutesCoercion ≡ false

canonicalFamilyStatementBoundary : FamilyStatementBoundary
canonicalFamilyStatementBoundary =
  familyStatementBoundary
    true refl
    false refl
    false refl
    false refl

------------------------------------------------------------------------
-- Case boundary manifest.
------------------------------------------------------------------------

record EskridgeEvidenceBoundary : Set where
  constructor eskridgeEvidenceBoundary
  field
    recordedTestimonyIsPrimaryEvidence : Bool
    recordedTestimonyIsPrimaryEvidenceIsTrue :
      recordedTestimonyIsPrimaryEvidence ≡ true
    primaryEvidenceAutomaticallyEstablishesHomicide : Bool
    primaryEvidenceAutomaticallyEstablishesHomicideIsFalse :
      primaryEvidenceAutomaticallyEstablishesHomicide ≡ false
    publicSuicideLabelAutomaticallyDiscreditsPreDeathTestimony : Bool
    publicSuicideLabelAutomaticallyDiscreditsPreDeathTestimonyIsFalse :
      publicSuicideLabelAutomaticallyDiscreditsPreDeathTestimony ≡ false
    missingPublicRecordsAutomaticallyValidateOfficialNarrative : Bool
    missingPublicRecordsAutomaticallyValidateOfficialNarrativeIsFalse :
      missingPublicRecordsAutomaticallyValidateOfficialNarrative ≡ false
    missingPublicRecordsAutomaticallyRefuteOfficialNarrative : Bool
    missingPublicRecordsAutomaticallyRefuteOfficialNarrativeIsFalse :
      missingPublicRecordsAutomaticallyRefuteOfficialNarrative ≡ false

canonicalEskridgeEvidenceBoundary : EskridgeEvidenceBoundary
canonicalEskridgeEvidenceBoundary =
  eskridgeEvidenceBoundary
    true refl
    false refl
    false refl
    false refl
    false refl
