module DASHI.Biology.KitzerowAttributionEvidenceLineageExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

import DASHI.Core.ReopenableConsumerInterventionKernelExact as Kernel
import DASHI.Core.AttributedPublicClaimExact as Public
import DASHI.Wikimedia.IbrahimSnowballSystematicReviewMetaAnalysisPublicationBiasBidiExact as Systematic
import DASHI.Law.SolomonIslandsDefeatMotionRepublicationIndependenceExact as Republication
import DASHI.Culture.WitchRelationalAttributionDialogueBidiExact as Relational
import DASHI.Biology.KitzerowPriorityAttributionExact as Priority

------------------------------------------------------------------------
-- KITZEROW ATTRIBUTION EVIDENCE LINEAGE
--
-- Cross-pollinates the repo's existing public-claim, republication,
-- relational-attribution and evidence-independence machinery into the Kitzerow
-- chronology/exposure lane. Publication/report multiplicity is not evidence
-- independence. Exposure is not derivation. A later reply/dispute creates a
-- new provenance event and cannot rewrite the earlier manifestation's history.
-- Exact text, near-text, idea/process/result reuse, generic structural
-- similarity and documented direct use remain different evidence classes.
------------------------------------------------------------------------

data AttributionEvidenceKind : Set where
  chronologyOnly : AttributionEvidenceKind
  publicAvailability : AttributionEvidenceKind
  originatorReportedContact : AttributionEvidenceKind
  authenticatedPrePublicationExposure : AttributionEvidenceKind
  authenticatedPostPublicationContact : AttributionEvidenceKind
  exactTextReuse : AttributionEvidenceKind
  nearVerbatimReuse : AttributionEvidenceKind
  ideaProcessResultReuse : AttributionEvidenceKind
  structuralSimilarityOnly : AttributionEvidenceKind
  documentedDirectUse : AttributionEvidenceKind
  independentConvergenceControl : AttributionEvidenceKind

data TemporalDirection : Set where
  beforeComparisonPublication : TemporalDirection
  afterComparisonPublication : TemporalDirection
  temporalOrderUnresolved : TemporalDirection

record AttributionLineageObservation : Set where
  constructor attributionLineageObservation
  field
    observationKey : String
    provenanceRoot : String
    evidenceKind : AttributionEvidenceKind
    temporalDirection : TemporalDirection
    exactArtifactReference : String
    interpretation : String

open AttributionLineageObservation public

stanfordOriginatorContactObservation : AttributionLineageObservation
stanfordOriginatorContactObservation =
  attributionLineageObservation
    "Stanford contact report"
    "Kitzerow originator public timeline"
    originatorReportedContact
    beforeComparisonPublication
    "public timeline points to a linked correspondence artifact; linked contents remain uninspected in the canonical acquisition status"
    "pays an originator-reported exposure hypothesis and acquisition target only; it does not pay authenticated contact, direct use or derivation"

brazilPostPublicationObservation : AttributionLineageObservation
brazilPostPublicationObservation =
  attributionLineageObservation
    "Brazil/MDPI post-publication correspondence report"
    "Kitzerow originator public timeline"
    originatorReportedContact
    afterComparisonPublication
    "underlying correspondence remains unacquired"
    "can pay later response/contact chronology if authenticated; by temporal direction alone it cannot establish exposure before the already-published comparison"

iaccOriginatorContactObservation : AttributionLineageObservation
iaccOriginatorContactObservation =
  attributionLineageObservation
    "IACC/MedMaps exposure-chain report"
    "Kitzerow originator public timeline"
    originatorReportedContact
    temporalOrderUnresolved
    "underlying message/export and institutional chronology remain unacquired"
    "remains a provenance acquisition lead; neither republication nor later institutional role supplies direct-use evidence"

nomuraIndependenceControlObservation : AttributionLineageObservation
nomuraIndependenceControlObservation =
  attributionLineageObservation
    "Nomura chronology independence control"
    "Nomura/Japan comparison research lineage"
    independentConvergenceControl
    beforeComparisonPublication
    "KitzerowPriorityAttributionExact.canonicalNomuraAttribution"
    "comparison chronology predates the relevant Kitzerow articulation and therefore functions as an independence-supporting convergence control, not as evidence against every possible shared upstream scientific source"

canonicalKitzerowAttributionObservations : List AttributionLineageObservation
canonicalKitzerowAttributionObservations =
  stanfordOriginatorContactObservation
  ∷ brazilPostPublicationObservation
  ∷ iaccOriginatorContactObservation
  ∷ nomuraIndependenceControlObservation
  ∷ []

------------------------------------------------------------------------
-- Generic provenance-root receipt: three named contact/exposure narratives can
-- still share one upstream root. Downstream multiplicity must not inflate the
-- count of independent evidence units.
------------------------------------------------------------------------

stanfordContactEvidenceItem : Kernel.EvidenceItem
stanfordContactEvidenceItem = Kernel.evidenceItem
  "Stanford originator-reported contact"
  "Kitzerow originator public timeline"
  Kernel.hypothesisEvidence
  Kernel.ignorance
  "originator report plus public link; linked artifact contents uninspected"
  "contact/exposure chronology only"

brazilContactEvidenceItem : Kernel.EvidenceItem
brazilContactEvidenceItem = Kernel.evidenceItem
  "Brazil/MDPI originator-reported correspondence"
  "Kitzerow originator public timeline"
  Kernel.hypothesisEvidence
  Kernel.ignorance
  "originator report; underlying post-publication correspondence unacquired"
  "later response/contact chronology only"

iaccContactEvidenceItem : Kernel.EvidenceItem
iaccContactEvidenceItem = Kernel.evidenceItem
  "IACC/MedMaps originator-reported exposure chain"
  "Kitzerow originator public timeline"
  Kernel.hypothesisEvidence
  Kernel.ignorance
  "originator report; underlying exposure artifact and chronology unacquired"
  "possible exposure-chain chronology only"

kitzerowContactEvidenceIndependence : Kernel.EvidenceIndependenceReceipt
kitzerowContactEvidenceIndependence = Kernel.evidenceIndependenceReceipt
  (stanfordContactEvidenceItem ∷ brazilContactEvidenceItem ∷ iaccContactEvidenceItem ∷ [])
  ("Kitzerow originator public timeline" ∷ [])
  "independence is counted at the upstream provenance root / independently inspected artifact or observation, not at the number of downstream claims, pages, publications or republications"
  true

record ContactIndependenceReceipt : Set where
  constructor contactIndependenceReceipt
  field
    genericReceipt : Kernel.EvidenceIndependenceReceipt
    contactReportMultiplicityInflatesIndependence : Bool
    contactReportMultiplicityInflatesIndependenceIsFalse :
      contactReportMultiplicityInflatesIndependence ≡ false
    reading : String

open ContactIndependenceReceipt public

canonicalKitzerowContactIndependenceReceipt : ContactIndependenceReceipt
canonicalKitzerowContactIndependenceReceipt =
  contactIndependenceReceipt
    kitzerowContactEvidenceIndependence
    false refl
    "Stanford, Brazil and IACC are distinct attribution questions but their currently canonical contact/exposure claims are not three independent authentications merely because they are separately narrated from the same originator provenance root"

------------------------------------------------------------------------
-- Temporal-direction and dialogue/provenance receipts.
------------------------------------------------------------------------

record DirectionalProvenance : Set where
  constructor directionalProvenance
  field
    targetReference : String
    knownContactDirection : TemporalDirection
    postPublicationContactPaysPrePublicationExposure : Bool
    postPublicationContactPaysPrePublicationExposureIsFalse :
      postPublicationContactPaysPrePublicationExposure ≡ false
    brazilNeedsEarlierExposureOrManuscriptHistory : Bool
    brazilNeedsEarlierExposureOrManuscriptHistoryIsTrue :
      brazilNeedsEarlierExposureOrManuscriptHistory ≡ true
    responseCreatesNewProvenanceWithoutRewritingEarlierManifestation : Bool
    responseCreatesNewProvenanceWithoutRewritingEarlierManifestationIsTrue :
      responseCreatesNewProvenanceWithoutRewritingEarlierManifestation ≡ true
    nextEvidence : String

open DirectionalProvenance public

canonicalBrazilDirectionalProvenance : DirectionalProvenance
canonicalBrazilDirectionalProvenance =
  directionalProvenance
    "Brazil BH4 ASD systematic review attribution"
    afterComparisonPublication
    false refl
    true refl
    true refl
    "to test derivation of the published review, acquire an authenticated exposure event that predates the relevant manuscript state and/or versioned manuscript/preprint history showing a traceable change; post-publication complaint/response correspondence creates a later provenance event but cannot retroactively create or rewrite earlier exposure/derivation"

------------------------------------------------------------------------
-- Cross-domain no-collapse boundary.
------------------------------------------------------------------------

record KitzerowAttributionLineageBoundary : Set where
  constructor kitzerowAttributionLineageBoundary
  field
    downstreamPublicationMultiplicityCreatesIndependentEvidence : Bool
    downstreamPublicationMultiplicityCreatesIndependentEvidenceIsFalse :
      downstreamPublicationMultiplicityCreatesIndependentEvidence ≡ false
    sameProvenanceRootMayBeCountedRepeatedlyAsIndependent : Bool
    sameProvenanceRootMayBeCountedRepeatedlyAsIndependentIsFalse :
      sameProvenanceRootMayBeCountedRepeatedlyAsIndependent ≡ false
    contactOrExposureAloneProvesDerivation : Bool
    contactOrExposureAloneProvesDerivationIsFalse :
      contactOrExposureAloneProvesDerivation ≡ false
    postPublicationContactProvesPrePublicationExposure : Bool
    postPublicationContactProvesPrePublicationExposureIsFalse :
      postPublicationContactProvesPrePublicationExposure ≡ false
    laterResponseRewritesEarlierProvenance : Bool
    laterResponseRewritesEarlierProvenanceIsFalse :
      laterResponseRewritesEarlierProvenance ≡ false
    authenticatedPrePublicationExposureAloneProvesDerivation : Bool
    authenticatedPrePublicationExposureAloneProvesDerivationIsFalse :
      authenticatedPrePublicationExposureAloneProvesDerivation ≡ false
    citationAbsenceAloneProvesPlagiarism : Bool
    citationAbsenceAloneProvesPlagiarismIsFalse :
      citationAbsenceAloneProvesPlagiarism ≡ false
    structuralSimilarityAloneProvesPlagiarism : Bool
    structuralSimilarityAloneProvesPlagiarismIsFalse :
      structuralSimilarityAloneProvesPlagiarism ≡ false
    ideaProcessResultReuseCanBeRelevantToPlagiarism : Bool
    ideaProcessResultReuseCanBeRelevantToPlagiarismIsTrue :
      ideaProcessResultReuseCanBeRelevantToPlagiarism ≡ true
    documentedDirectUseCanUpgradeDerivation : Bool
    documentedDirectUseCanUpgradeDerivationIsTrue :
      documentedDirectUseCanUpgradeDerivation ≡ true
    sourceLineageMustBePreserved : Bool
    sourceLineageMustBePreservedIsTrue : sourceLineageMustBePreserved ≡ true
    mediaOrPublicInvestigationSubstitutesForPrimaryProvenanceArtifact : Bool
    mediaOrPublicInvestigationSubstitutesForPrimaryProvenanceArtifactIsFalse :
      mediaOrPublicInvestigationSubstitutesForPrimaryProvenanceArtifact ≡ false

open KitzerowAttributionLineageBoundary public

canonicalKitzerowAttributionLineageBoundary : KitzerowAttributionLineageBoundary
canonicalKitzerowAttributionLineageBoundary =
  kitzerowAttributionLineageBoundary
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    false refl
    true refl
    true refl
    true refl
    false refl

------------------------------------------------------------------------
-- Existing generic owners are deliberately consumed rather than duplicated.
------------------------------------------------------------------------

genericEvidenceKernelBoundary : Kernel.ReopenableConsumerInterventionBoundary
genericEvidenceKernelBoundary = Kernel.canonicalReopenableConsumerInterventionBoundary

systematicReviewIndependenceBoundary : Systematic.SystematicReviewMetaAnalysisBoundary
systematicReviewIndependenceBoundary = Systematic.canonicalSystematicReviewMetaAnalysisBoundary

priorityAttributionFirewall : Priority.AttributionFirewall
priorityAttributionFirewall = Priority.canonicalAttributionFirewall

publicClaimBoundary : Public.PublicClaimBoundary
publicClaimBoundary = Public.canonicalPublicClaimBoundary

republicationState : Republication.CurrentRepublicationState
republicationState = Republication.currentRepublicationState

relationalAttributionBoundary : Relational.WitchRelationalAttributionBoundary
relationalAttributionBoundary = Relational.canonicalWitchRelationalAttributionBoundary
