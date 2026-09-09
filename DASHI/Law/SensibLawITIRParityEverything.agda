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
