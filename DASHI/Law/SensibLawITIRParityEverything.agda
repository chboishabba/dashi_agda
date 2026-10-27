module DASHI.Law.SensibLawITIRParityEverything where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (false; true)
open import Agda.Builtin.Equality using (_≡_; refl)

import DASHI.Law.SensibLawAgdaFirstLegalRuntimeEverything as LegalRuntime
import DASHI.Interop.ITIRSuiteNormalizedCompilerParityExact as ITIRParity
import DASHI.Interop.ITIRSuiteNormalizedCompilerStageParityWitnessExact as StageParity
import DASHI.Interop.ITIRRecordingManifestSensibLawAdapterExact as RecordingParity
import DASHI.Interop.ITIRTemporalHealthSensibLawAdapterExact as HealthParity
import DASHI.Interop.ITIRSubmittedEvidencePackageSensibLawAdapterExact as PackageParity
import DASHI.Interop.ITIRHousingEpisodeSensibLawAdapterExact as HousingParity
import DASHI.Interop.ITIRLaterMedicalParticularHarmSensibLawAdapterExact as LaterMedicalParity
import DASHI.Interop.ITIRHealthRecordSensibLawAdapterExact as GenericHealthParity
import DASHI.Interop.SensibLawHealthEvidenceProcessorParityExact as ProcessorParity
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesNarrativeGovernanceWeldExact as FriendlyjordiesNarrative
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesCompetingNarrativeExact as FriendlyjordiesCompeting
import DASHI.Cognition.PNF.SensibLawFriendlyjordiesSourceTotalityExact as FriendlyjordiesSourceTotality
import DASHI.Law.SensibLawRealMatterReviewDecisionExact as RealMatterReview
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as ExpertProduction
import DASHI.Governance.LegalDecisionDoubleProjectionExact as LegalDecision
import DASHI.Governance.LegitimacyEvidenceSeparationExact as Legitimacy
import DASHI.Core.IntersectionalNonFactorability as NF
import DASHI.Governance.PromotionSpine as Promotion
import DASHI.Foundations.CanonicalProvenancePromotion as Canonical
import DASHI.Governance.GovernedArtifactCore as Governed

------------------------------------------------------------------------
-- Terminal parity surface for the current housing / ITIR / SensibLaw tranche.
-- Importing this module requires all boundaries to coexist with the existing
-- Agda-first legal runtime; none replaces another owner.
------------------------------------------------------------------------

selectedLegalRuntimeContract : LegalRuntime.AgdaFirstLegalRuntimeContract
selectedLegalRuntimeContract = LegalRuntime.canonicalAgdaFirstLegalRuntimeContract

selectedITIRNormalizedParity : ITIRParity.ITIRSuiteNormalizedParityBoundary
selectedITIRNormalizedParity = ITIRParity.canonicalITIRSuiteNormalizedParityBoundary

selectedStageParityWitness : StageParity.NormalizedStageParityWitness
selectedStageParityWitness = StageParity.canonicalNormalizedStageParityWitness

selectedOwnerParityWitness : StageParity.CurrentLaneOwnerParity
selectedOwnerParityWitness = StageParity.canonicalCurrentLaneOwnerParity

selectedRecordingParity : RecordingParity.ITIRRecordingSensibLawParityBoundary
selectedRecordingParity = RecordingParity.canonicalITIRRecordingSensibLawParityBoundary

selectedTemporalHealthParity : HealthParity.ITIRTemporalHealthSensibLawParityBoundary
selectedTemporalHealthParity = HealthParity.canonicalITIRTemporalHealthSensibLawParityBoundary

selectedSubmittedEvidencePackageParity :
  PackageParity.ITIRSubmittedEvidencePackageParityBoundary
selectedSubmittedEvidencePackageParity =
  PackageParity.canonicalITIRSubmittedEvidencePackageParityBoundary

selectedHousingEpisodeParity : HousingParity.ITIRHousingEpisodeParityBoundary
selectedHousingEpisodeParity = HousingParity.canonicalITIRHousingEpisodeParityBoundary

selectedLaterMedicalParticularHarmParity :
  LaterMedicalParity.ITIRLaterMedicalParticularHarmParityBoundary
selectedLaterMedicalParticularHarmParity =
  LaterMedicalParity.canonicalITIRLaterMedicalParticularHarmParityBoundary

selectedGenericHealthRecordParity :
  GenericHealthParity.ITIRHealthRecordParityBoundary
selectedGenericHealthRecordParity =
  GenericHealthParity.canonicalITIRHealthRecordParityBoundary

selectedHealthEvidenceProcessorParity :
  ProcessorParity.HealthEvidenceProcessorParityBoundary
selectedHealthEvidenceProcessorParity =
  ProcessorParity.canonicalHealthEvidenceProcessorParityBoundary

selectedFriendlyjordiesNarrativeGovernanceBoundary :
  FriendlyjordiesNarrative.FriendlyjordiesNarrativeGovernanceBoundary
selectedFriendlyjordiesNarrativeGovernanceBoundary =
  FriendlyjordiesNarrative.canonicalFriendlyjordiesNarrativeGovernanceBoundary

selectedFriendlyjordiesCompetingNarrativeBoundary :
  FriendlyjordiesCompeting.FriendlyjordiesSensibLawBoundary
selectedFriendlyjordiesCompetingNarrativeBoundary =
  FriendlyjordiesCompeting.canonicalFriendlyjordiesSensibLawBoundary



selectedFriendlyjordiesSourceTotality :
  FriendlyjordiesSourceTotality.SourceTotalComparison
selectedFriendlyjordiesSourceTotality =
  FriendlyjordiesSourceTotality.canonicalFriendlyjordiesSourceTotality


selectedFriendlyjordiesConstructiveSourceTotalityBoundary :
  FriendlyjordiesSourceTotality.ConstructiveSourceTotalityBoundary
selectedFriendlyjordiesConstructiveSourceTotalityBoundary =
  FriendlyjordiesSourceTotality.canonicalConstructiveSourceTotalityBoundary

selectedFriendlyjordiesResidualAcquisitionClosure :
  FriendlyjordiesSourceTotality.ResidualAcquisitionClosure
selectedFriendlyjordiesResidualAcquisitionClosure =
  FriendlyjordiesSourceTotality.canonicalResidualAcquisitionClosure


------------------------------------------------------------------------
-- Canonical legal-governance semantic handoff.
--
-- Reuse existing owners.
-- Do not create an Actionstep-specific ontology.
-- Runtime parity, semantic promotion, legal citation, compliance, and domain
-- authority remain separate proof coordinates.
------------------------------------------------------------------------

open import DASHI.Interop.SensibLawSemanticPromotionPolicy public using
  ( SemanticPromotionPolicySurface
  ; semanticPromotionPolicySurface
  ; heuristic-only-abstains
  ; promotion-ignores-heuristic-bits
  ; semantic-promotion-truth-authority-closed
  ; semantic-promotion-legal-authority-closed
  ; semantic-promotion-all-authority-closed
  )

open import DASHI.Core.CompositionalComplianceExact public using
  ( CertifiedStage
  ; CompositeCompliance
  ; composeCertifiedStages
  ; DependentCertifiedStage
  )

open import DASHI.Law.LegalAuthorityCitationExact public using
  ( LegalCitation
  ; LegalAuthorityUseReceipt
  ; LegalCitationBoundary
  ; canonicalLegalCitationBoundary
  )

import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain

selectedDomainTransportReceipt : Domain.DomainTransportReceipt
selectedDomainTransportReceipt = Domain.canonicalDomainTransportReceipt

selectedRepresentationEqualityCreatesLegalAuthorityIsFalse :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority
    selectedDomainTransportReceipt ≡ false
selectedRepresentationEqualityCreatesLegalAuthorityIsFalse = refl

selectedVendorIdentityCreatesAuthorityIsFalse :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
    selectedDomainTransportReceipt ≡ false
selectedVendorIdentityCreatesAuthorityIsFalse = refl

selectedTargetDomainNeedsOwnAuthorityWitnessIsTrue :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    selectedDomainTransportReceipt ≡ true
selectedTargetDomainNeedsOwnAuthorityWitnessIsTrue = refl

------------------------------------------------------------------------
-- Exact legal/compliance non-promotion handoff.
-- Reuse canonical owners. These proofs do not create vendor semantics.
------------------------------------------------------------------------

selectedLegalReviewDoesNotCreateClaimTruth :
  RealMatterReview.LegalReviewDecisionCreatesClaimTruth → ⊥
selectedLegalReviewDoesNotCreateClaimTruth =
  RealMatterReview.legalReviewDecisionDoesNotCreateClaimTruth

selectedQualificationDoesNotAutomaticallyProveForensicCompliance :
  ExpertProduction.QualificationAutomaticallyForensicCompliance → ⊥
selectedQualificationDoesNotAutomaticallyProveForensicCompliance =
  ExpertProduction.qualificationDoesNotAutomaticallyProveForensicCompliance

selectedReportAdmissionDoesNotRepairMissingInput :
  ExpertProduction.ReportAdmissionRepairsMissingInput → ⊥
selectedReportAdmissionDoesNotRepairMissingInput =
  ExpertProduction.reportAdmissionDoesNotRepairMissingInput

selectedOfficialLegalSurfaceDoesNotRecoverFineState :
  NF.FactorsThrough
    LegalDecision.officialSurface
    LegalDecision.fineLegalStateOf
  → ⊥
selectedOfficialLegalSurfaceDoesNotRecoverFineState =
  LegalDecision.officialSurfaceCannotRecoverFineLegalState

selectedOfficialActionDoesNotRecoverAutonomyAndAuthority :
  NF.FactorsThrough
    LegalDecision.autonomyOfficialSurface
    LegalDecision.fineAutonomyLegalStateOf
  → ⊥
selectedOfficialActionDoesNotRecoverAutonomyAndAuthority =
  LegalDecision.officialActionCannotRecoverAutonomyAndAuthority

selectedLegalityAloneDoesNotCreateLegitimacy :
  Legitimacy.AdmittedLegitimacy
    Legitimacy.demoEvidence
    Legitimacy.legalOnly
  → ⊥
selectedLegalityAloneDoesNotCreateLegitimacy =
  Legitimacy.legalOnlyIsNotAdmittedLegitimacy

selectedMissingAdmissibilityStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true false true true true)
  ≡ Governed.abstain
selectedMissingAdmissibilityStillAbstains =
  Promotion.missingAdmissibilityAbstains

selectedMissingValidationStillAbstains :
  Promotion.authorizationFromObligations
    (Canonical.promotionObligations true true true true false)
  ≡ Governed.abstain
selectedMissingValidationStillAbstains =
  Promotion.missingValidationAbstains
