module DASHI.Physics.ExoticGravity.AntigravitySourceAcquisitionCompilationExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.AntigravityFirstIrreducibleSourceResidualExact as Source
import DASHI.Physics.ExoticGravity.AntigravityOptimizedAcquisitionPlanExact as Plan
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

------------------------------------------------------------------------
-- EMPIRICAL SOURCE PACKAGE -> FULL SOURCE/GEOMETRY BUNDLE
--
-- Apparatus identity and run identity are distinct coordinates.  The apparatus
-- persists across runs; a run identifies one execution on that apparatus.
------------------------------------------------------------------------

record SourceMeasurementProvenance : Set where
  constructor source-measurement-provenance
  field
    responsibleBody : String
    apparatusIdentityCarrier : String
    runIdentifier : String
    rawDataCarrier : String
    rawDataHash : String
    dataRevision : String
    instrumentConfigurationCarrier : String
    calibrationCarrier : String
    calibrationRevision : String
    sourceReconstructionCarrier : String
    inspectionOrAnalysisReceipt : String

open SourceMeasurementProvenance public

record SourceAcquisitionReceipt : Set where
  constructor source-acquisition-receipt
  field
    target : Source.SourceAcquisitionTarget
    apparatusCarrier : String
    targetApparatusMatches :
      Source.apparatusCarrier target ≡ apparatusCarrier

    provenance : SourceMeasurementProvenance
    provenanceApparatusMatchesReceipt :
      apparatusIdentityCarrier provenance ≡ apparatusCarrier

    shapeMeasurementCarrier : String
    shapeCarrierMatchesTarget :
      shapeMeasurementCarrier ≡ Source.exactShapeCarrier target

    sourceDistributionMeasurementCarrier : String
    sourceDistributionCarrierMatchesTarget :
      sourceDistributionMeasurementCarrier
        ≡ Source.sourceDistributionCarrier target

    massCurrentMeasurementCarrier : String
    massCurrentCarrierMatchesTarget :
      massCurrentMeasurementCarrier ≡ Source.massCurrentCarrier target

    stressEnergyReconstructionCarrier : String
    stressEnergyCarrierMatchesTarget :
      stressEnergyReconstructionCarrier ≡ Source.stressEnergyCarrier target

    probeGeometryMeasurementCarrier : String
    probeGeometryCarrierMatchesTarget :
      probeGeometryMeasurementCarrier ≡ Source.probeGeometryCarrier target

    calibrationRevisionMatchesTarget :
      calibrationRevision provenance ≡ Source.calibrationRevision target

    sameApparatusIdentityMatchesTarget :
      apparatusIdentityCarrier provenance ≡ Source.sameApparatusIdentityCarrier target

    compiledBundle : Plan.FullSourceGeometryBundleReceipt
    compiledBundleCarrierMatches :
      Plan.FullSourceGeometryBundleReceipt.apparatusCarrier compiledBundle
        ≡ apparatusCarrier

open SourceAcquisitionReceipt public

compileSourceAcquisition :
  SourceAcquisitionReceipt → Plan.FullSourceGeometryBundleReceipt
compileSourceAcquisition receipt = compiledBundle receipt

------------------------------------------------------------------------
-- Reverse residuals for producing a real receipt.
------------------------------------------------------------------------

data SourceAcquisitionCompilationResidual : Set where
  missingResponsibleBody : SourceAcquisitionCompilationResidual
  missingApparatusIdentity : SourceAcquisitionCompilationResidual
  missingRunIdentity : SourceAcquisitionCompilationResidual
  missingRawDataCarrier : SourceAcquisitionCompilationResidual
  missingRawDataHash : SourceAcquisitionCompilationResidual
  missingCalibrationCarrier : SourceAcquisitionCompilationResidual
  missingCalibrationRevision : SourceAcquisitionCompilationResidual
  missingInstrumentConfiguration : SourceAcquisitionCompilationResidual
  missingSourceReconstruction : SourceAcquisitionCompilationResidual
  missingShapeMeasurement : SourceAcquisitionCompilationResidual
  missingSourceDistributionMeasurement : SourceAcquisitionCompilationResidual
  missingMassCurrentMeasurement : SourceAcquisitionCompilationResidual
  missingStressEnergyReconstruction : SourceAcquisitionCompilationResidual
  missingProbeGeometryMeasurement : SourceAcquisitionCompilationResidual
  missingPerConsumerBundleWitnesses : SourceAcquisitionCompilationResidual

producerForSourceCompilationResidual :
  SourceAcquisitionCompilationResidual → Search.ProducerClass
producerForSourceCompilationResidual missingResponsibleBody = Search.attributionProducer
producerForSourceCompilationResidual missingApparatusIdentity = Search.identityProducer
producerForSourceCompilationResidual missingRunIdentity = Search.identityProducer
producerForSourceCompilationResidual missingRawDataCarrier = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingRawDataHash = Search.identityProducer
producerForSourceCompilationResidual missingCalibrationCarrier = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingCalibrationRevision = Search.temporalProducer
producerForSourceCompilationResidual missingInstrumentConfiguration = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingSourceReconstruction = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingShapeMeasurement = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingSourceDistributionMeasurement = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingMassCurrentMeasurement = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingStressEnergyReconstruction = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingProbeGeometryMeasurement = Search.empiricalEvidenceProducer
producerForSourceCompilationResidual missingPerConsumerBundleWitnesses = Search.identityProducer

------------------------------------------------------------------------
-- Current repo state: no canonical physical source package is manufactured.
------------------------------------------------------------------------

data CurrentSourceAcquisitionReceiptAuthority : Set where

noCurrentCanonicalSourceAcquisitionReceipt :
  CurrentSourceAcquisitionReceiptAuthority → SourceAcquisitionReceipt
noCurrentCanonicalSourceAcquisitionReceipt ()

record SourceAcquisitionCompilationBoundary : Set where
  constructor source-acquisition-compilation-boundary
  field
    targetDescriptionEqualsMeasurementReceipt : Bool
    apparatusIdentityEqualsRunIdentifier : Bool
    calibrationCarrierEqualsCalibrationRevision : Bool
    localMeasurementNeedsRunHashRevisionProvenance : Bool
    sameApparatusIdentityRequired : Bool
    perConsumerBundleWitnessesRequired : Bool
    sourcePackageMayCompileToBundleOne : Bool
    compiledBundleAutomaticallyProvesAntigravity : Bool
    currentRepoContainsCanonicalPhysicalSourcePackage : Bool

canonicalSourceAcquisitionCompilationBoundary :
  SourceAcquisitionCompilationBoundary
canonicalSourceAcquisitionCompilationBoundary =
  source-acquisition-compilation-boundary
    false false false true true true true false false
