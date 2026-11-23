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
import DASHI.Law.AIHumanCorporateAttributionSensibLaw2026Exact as AIAgentAttribution
import DASHI.Law.AustralianCommonwealthAgentComputerOffenceAttribution2026Exact as CommonwealthAgentLaw
import DASHI.Law.OpenAIMedicareParliamentaryEvidence20261006Exact as MedicareHearing
import DASHI.Law.AIAgentLegalAcquisitionProgress20261012Exact as AILegalProgress

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

-- AI-agent legal attribution is carried through the same SensibLaw parity
-- surface. The primary-law owner pays the candidate statutory structure;
-- hearing evidence separately pays post-incident response facts without
-- back-propagating them into June fault or liability.
selectedMedicareAIAgentLegalBoundary :
  AIAgentAttribution.NamedIncidentLegalBoundary
selectedMedicareAIAgentLegalBoundary =
  AIAgentAttribution.medicareLegalAttributionBoundary

selectedMedicare4781Boundary :
  CommonwealthAgentLaw.Section4781ApplicationBoundary
selectedMedicare4781Boundary =
  CommonwealthAgentLaw.medicare4781ApplicationBoundary

selectedMedicareParliamentaryResponse :
  MedicareHearing.ParliamentaryResponseEvidence
selectedMedicareParliamentaryResponse =
  MedicareHearing.openAIParliamentaryResponseEvidence

selectedCandidateOffenceSourceProgress :
  AILegalProgress.LegalProducerProgress
selectedCandidateOffenceSourceProgress =
  AILegalProgress.candidateOffenceSourceAcquired

selectedPostIncidentResponseProgress :
  AILegalProgress.LegalProducerProgress
selectedPostIncidentResponseProgress =
  AILegalProgress.postIncidentOrganisationalResponse

selectedCorporateFaultProgress :
  AILegalProgress.LegalProducerProgress
selectedCorporateFaultProgress =
  AILegalProgress.corporateFaultStillOpen
