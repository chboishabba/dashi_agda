module DASHI.Law.SensibLawITIRParityEverything where

open import DASHI.Core.Prelude

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
import DASHI.Core.InstitutionalNormProductionExact as InstitutionalNorm
import DASHI.Core.InstitutionalStatusSignalAdequacyExact as StatusSignal
import DASHI.Core.InstitutionalProximityInfluenceAdequacyExact as ProximityInfluence
import DASHI.Law.SensibLawLegalReasonablenessNormativityBridgeExact as LegalNormativity
import DASHI.Law.SensibLawOperationalLegalityExact as OperationalLegality
import DASHI.Law.SensibLawInstitutionalResponsibilityExact as InstitutionalResponsibility
import DASHI.Law.SensibLawEpistemicConsequenceBoundaryExact as EpistemicConsequence

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
-- Reuse existing owners. Do not create an Actionstep-specific ontology.
-- Runtime parity, semantic promotion, legal citation, and compliance remain
-- separate proof coordinates.
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


------------------------------------------------------------------------
-- Current TOE governance convergence.
--
-- Reuse source-owned firewalls.
-- Do not create Actionstep, evidence, authority, or provenance semantics here.
------------------------------------------------------------------------

import DASHI.Cognition.PNF.SensibLawLegalSourceAuthorityEvidenceExact as LegalAuthority
import DASHI.Governance.DomainPermeabilityAuthorityTransport as Domain
import DASHI.Core.SnowballAttributionProvenanceInvariantExact as Snowball
import DASHI.Interop.SensibLawSnowballAttributionLineageAdapterExact as SnowballLineage
import DASHI.Law.SensibLawParetoProofDirectedCorpusSearchEverything as ParetoSearch
import DASHI.Law.SensibLawNativeLegalFollowCLIExact as NativeFollow
import DASHI.Law.SensibLawPreferredAustralianAuthorityAcquisitionExact as Acquisition
import DASHI.Law.SensibLawExpertEvidenceProductionIntegrityExact as Expert
import DASHI.Interop.SLRCanonicalEvidenceSubstrateExact as Evidence
import DASHI.Core.FrozenProvenanceDynamicRefinementExact as Future

selectedLegalSourceAuthorityBoundary :
  LegalAuthority.LegalSourceAuthorityBoundary
selectedLegalSourceAuthorityBoundary =
  LegalAuthority.canonicalLegalSourceAuthorityBoundary

selectedDomainTransportReceipt :
  Domain.DomainTransportReceipt
selectedDomainTransportReceipt =
  Domain.canonicalDomainTransportReceipt

selectedAttributionSnowballBoundary :
  Snowball.AttributionSnowballBoundary
selectedAttributionSnowballBoundary =
  Snowball.canonicalAttributionSnowballBoundary

selectedSnowballLineageBoundary :
  SnowballLineage.SensibLawSnowballLineageBoundary
selectedSnowballLineageBoundary =
  SnowballLineage.canonicalSensibLawSnowballLineageBoundary

selectedNativeLegalFollowBoundary :
  NativeFollow.NativeLegalFollowCliBoundary
selectedNativeLegalFollowBoundary =
  NativeFollow.canonicalNativeLegalFollowCliBoundary

selectedProviderFailureCalibration :
  Acquisition.ProviderFailureCalibration
selectedProviderFailureCalibration =
  Acquisition.canonicalProviderFailureCalibration

selectedExpertProductionBoundary :
  Expert.ExpertProductionBoundary
selectedExpertProductionBoundary =
  Expert.canonicalExpertProductionBoundary

selectedCanonicalEvidenceBoundary :
  Evidence.SLRCanonicalEvidenceBoundary
selectedCanonicalEvidenceBoundary =
  Evidence.canonicalSLRCanonicalEvidenceBoundary

selectedFrozenProvenanceDynamicBoundary :
  Future.FrozenProvenanceDynamicBoundary
selectedFrozenProvenanceDynamicBoundary =
  Future.canonicalFrozenProvenanceDynamicBoundary

governanceCandidateSourceDoesNotCloseAuthority :
  LegalAuthority.CandidateSourceIsAuthoritative → ⊥
governanceCandidateSourceDoesNotCloseAuthority =
  LegalAuthority.candidateSourceDoesNotCloseAuthority

governanceSameSystemDoesNotCloseAuthority :
  LegalAuthority.SameLegalSystemAutomaticallyMeansAuthority → ⊥
governanceSameSystemDoesNotCloseAuthority =
  LegalAuthority.sameSystemDoesNotAutomaticallyCloseAuthority

governanceCurrentValidityDoesNotEstablishApplicability :
  LegalAuthority.CurrentValidityAutomaticallyMeansApplicability → ⊥
governanceCurrentValidityDoesNotEstablishApplicability =
  LegalAuthority.currentValidityDoesNotAutomaticallyEstablishApplicability

governanceSemanticAdmissionDoesNotCreateLegalAuthority :
  LegalAuthority.SemanticAdmissionAuthorityIsLegalSourceAuthority → ⊥
governanceSemanticAdmissionDoesNotCreateLegalAuthority =
  LegalAuthority.semanticAdmissionDoesNotBecomeLegalSourceAuthority

governanceDocumentRoleDoesNotCreateLegalAuthority :
  LegalAuthority.DocumentRoleSuppliesLegalSourceAuthority → ⊥
governanceDocumentRoleDoesNotCreateLegalAuthority =
  LegalAuthority.documentRoleDoesNotSupplyLegalSourceAuthority

governanceRuntimeCannotInventLegalSemantics :
  LegalRuntime.AgdaFirstLegalRuntimeContract.runtimeMayInventMissingFormalLegalSemantics
    selectedLegalRuntimeContract
  ≡ false
governanceRuntimeCannotInventLegalSemantics =
  LegalRuntime.AgdaFirstLegalRuntimeContract.runtimeMayInventMissingFormalLegalSemanticsIsFalse
    selectedLegalRuntimeContract

governanceSourceFollowCannotBecomeAuthorityByTransport :
  LegalRuntime.AgdaFirstLegalRuntimeContract.sourceFollowMayBecomeAuthorityByTransport
    selectedLegalRuntimeContract
  ≡ false
governanceSourceFollowCannotBecomeAuthorityByTransport =
  LegalRuntime.AgdaFirstLegalRuntimeContract.sourceFollowMayBecomeAuthorityByTransportIsFalse
    selectedLegalRuntimeContract

governanceRepresentationEqualityDoesNotCreateLegalAuthority :
  Domain.DomainTransportReceipt.representationEqualityCreatesLegalAuthority
    selectedDomainTransportReceipt
  ≡ false
governanceRepresentationEqualityDoesNotCreateLegalAuthority = refl

governanceVendorIdentityDoesNotCreateAuthority :
  Domain.DomainTransportReceipt.vendorIdentityCreatesAuthority
    selectedDomainTransportReceipt
  ≡ false
governanceVendorIdentityDoesNotCreateAuthority = refl

governanceTargetDomainNeedsOwnAuthorityWitness :
  Domain.DomainTransportReceipt.targetDomainNeedsOwnAuthorityWitness
    selectedDomainTransportReceipt
  ≡ true
governanceTargetDomainNeedsOwnAuthorityWitness = refl

governanceSnowballCitationDoesNotCreateAuthority :
  Snowball.citationMayCreateAuthority selectedAttributionSnowballBoundary
  ≡ false
governanceSnowballCitationDoesNotCreateAuthority = refl

governanceSnowballCitationDoesNotCreateLegalAuthority :
  SnowballLineage.SensibLawSnowballLineageBoundary.citationCreatesLegalAuthority
    selectedSnowballLineageBoundary
  ≡ false
governanceSnowballCitationDoesNotCreateLegalAuthority = refl

governanceParetoDirectiveIsNotLegalAuthority :
  ParetoSearch.SearchDirectiveIsLegalAuthority → ⊥
governanceParetoDirectiveIsNotLegalAuthority =
  ParetoSearch.directiveIsNotAuthority

governanceParetoFrontierDoesNotPrejudgeRetrieval :
  ParetoSearch.FrontierCertificateMakesRetrievedSourceTrue → ⊥
governanceParetoFrontierDoesNotPrejudgeRetrieval =
  ParetoSearch.frontierCertificateDoesNotPrejudgeRetrieval

governanceNativeCliDoesNotCreateLegalAuthority :
  NativeFollow.NativeCliAutomaticallyLegalAuthority → ⊥
governanceNativeCliDoesNotCreateLegalAuthority =
  NativeFollow.nativeCliDoesNotCreateAuthority

governanceProviderFailureDoesNotMakePropositionFalse :
  Acquisition.ProviderFailureAutomaticallyPropositionFalse → ⊥
governanceProviderFailureDoesNotMakePropositionFalse =
  Acquisition.providerFailureDoesNotMakePropositionFalse

governanceExpertProductionPromotesNoAuthority :
  Expert.expertProductionPromotesAnyAuthority ≡ false
governanceExpertProductionPromotesNoAuthority =
  Expert.expertProductionPromotesAnyAuthorityIsFalse

governanceMultipleReportsDoNotCreateIndependence :
  Expert.MultipleReportsAutomaticallyIndependent → ⊥
governanceMultipleReportsDoNotCreateIndependence =
  Expert.multipleReportsDoNotAutomaticallyCreateIndependence

governanceManifestationDoesNotCreateSemanticAuthority :
  Evidence.ManifestationCreatesSemanticAuthority → ⊥
governanceManifestationDoesNotCreateSemanticAuthority =
  Evidence.manifestationDoesNotCreateSemanticAuthority

governanceObservationDoesNotCreateClaimTruth :
  Evidence.ObservationCreatesClaimTruth → ⊥
governanceObservationDoesNotCreateClaimTruth =
  Evidence.observationDoesNotCreateClaimTruth

governanceObservationDoesNotPromoteApplicability :
  Evidence.ObservationPromotesApplicability → ⊥
governanceObservationDoesNotPromoteApplicability =
  Evidence.observationDoesNotPromoteApplicability

governanceCanonicalEvidenceDoesNotCreateDigitalESDAdmission :
  Evidence.CanonicalEvidenceCreatesDigitalESDAdmission → ⊥
governanceCanonicalEvidenceDoesNotCreateDigitalESDAdmission =
  Evidence.canonicalEvidenceDoesNotCreateDigitalESDAdmission

governanceStaticSeparationDoesNotCreateDynamicSafety :
  Future.StaticSeparationCreatesDynamicSafetyPermission → ⊥
governanceStaticSeparationDoesNotCreateDynamicSafety =
  Future.staticSeparationDoesNotCreateDynamicSafety

governanceFrozenSelectionDoesNotCreateDynamicSafety :
  Future.FrozenSelectionCreatesDynamicSafetyPermission → ⊥
governanceFrozenSelectionDoesNotCreateDynamicSafety =
  Future.frozenSelectionDoesNotCreateDynamicSafety

governanceProvenanceAxisDoesNotCreateTruth :
  Future.ProvenanceAxisCreatesTruthPermission → ⊥
governanceProvenanceAxisDoesNotCreateTruth =
  Future.provenanceAxisDoesNotCreateTruth

governanceCrossPollinationDoesNotTransferAuthorship :
  Future.InRepoCrossPollinationTransfersAuthorshipPermission → ⊥
governanceCrossPollinationDoesNotTransferAuthorship =
  Future.crossPollinationDoesNotTransferAuthorship


------------------------------------------------------------------------
-- TOE institutional normativity handoff.
--
-- Reuse canonical owners.  This aggregate does not define a second
-- reasonableness, influence, enforcement, responsibility, or consequence
-- calculus.  It exposes only source-owned boundaries and exact non-promotion.
------------------------------------------------------------------------

selectedInstitutionalNormProductionBoundary :
  InstitutionalNorm.InstitutionalNormProductionBoundary
selectedInstitutionalNormProductionBoundary =
  InstitutionalNorm.canonicalInstitutionalNormProductionBoundary

selectedStatusSignalBoundary :
  StatusSignal.InstitutionalStatusSignalBoundary
selectedStatusSignalBoundary =
  StatusSignal.canonicalInstitutionalStatusSignalBoundary

selectedProximityInfluenceBoundary :
  ProximityInfluence.InstitutionalProximityBoundary
selectedProximityInfluenceBoundary =
  ProximityInfluence.canonicalInstitutionalProximityBoundary

selectedLegalReasonablenessNormativityBoundary :
  LegalNormativity.LegalReasonablenessNormativityBoundary
selectedLegalReasonablenessNormativityBoundary =
  LegalNormativity.canonicalLegalReasonablenessNormativityBoundary

selectedOperationalLegalityBoundary :
  OperationalLegality.OperationalLegalityBoundary
selectedOperationalLegalityBoundary =
  OperationalLegality.canonicalOperationalLegalityBoundary

selectedInstitutionalResponsibilityBoundary :
  InstitutionalResponsibility.InstitutionalResponsibilityBoundary
selectedInstitutionalResponsibilityBoundary =
  InstitutionalResponsibility.canonicalInstitutionalResponsibilityBoundary

selectedEpistemicConsequenceBoundary :
  EpistemicConsequence.EpistemicConsequenceBoundary
selectedEpistemicConsequenceBoundary =
  EpistemicConsequence.canonicalEpistemicConsequenceBoundary

governanceBaselineDoesNotRecoverProductionHistory :
  InstitutionalNorm.ProductionHistoryQueryAdequate → ⊥
governanceBaselineDoesNotRecoverProductionHistory =
  InstitutionalNorm.productionHistoryNotAdequate

governanceStatusDoesNotRecoverSubstantiveAdequacy :
  StatusSignal.SubstantiveAdequacyThroughStatus → ⊥
governanceStatusDoesNotRecoverSubstantiveAdequacy =
  StatusSignal.substantiveAdequacyDoesNotFactorThroughStatus

governanceProximityDoesNotCreateInfluence :
  ProximityInfluence.InfluenceThroughProximity → ⊥
governanceProximityDoesNotCreateInfluence =
  ProximityInfluence.influenceDoesNotFactorThroughProximity

governanceLegalValidityDoesNotCreatePoliticalNeutrality :
  InstitutionalNorm.legalValidityAutomaticallyPoliticalNeutrality
    selectedInstitutionalNormProductionBoundary
  ≡ false
governanceLegalValidityDoesNotCreatePoliticalNeutrality = refl

governanceStatusSignalDoesNotCreateSubstantiveAdequacy :
  StatusSignal.statusSignalAutomaticallySubstantiveAdequacy
    selectedStatusSignalBoundary
  ≡ false
governanceStatusSignalDoesNotCreateSubstantiveAdequacy = refl

governanceLawfulRangeDoesNotCreatePoliticalNeutrality :
  LegalNormativity.lawfulRangeAutomaticallyPoliticalNeutrality
    selectedLegalReasonablenessNormativityBoundary
  ≡ false
governanceLawfulRangeDoesNotCreatePoliticalNeutrality = refl

governanceFormalProhibitionDoesNotCreateEffectivePrevention :
  OperationalLegality.formalProhibitionAutomaticallyEffectivePrevention
    selectedOperationalLegalityBoundary
  ≡ false
governanceFormalProhibitionDoesNotCreateEffectivePrevention = refl

governanceAuthorisationDoesNotCreateJustification :
  InstitutionalResponsibility.authorisedAutomaticallyJustified
    selectedInstitutionalResponsibilityBoundary
  ≡ false
governanceAuthorisationDoesNotCreateJustification = refl

governanceHighUncertaintyDoesNotAutomaticallyEstablishIllegality :
  EpistemicConsequence.highUncertaintyAutomaticallyEstablishesIllegality
    selectedEpistemicConsequenceBoundary
  ≡ false
governanceHighUncertaintyDoesNotAutomaticallyEstablishIllegality = refl
