module DASHI.Physics.ExoticGravity.AntigravityFirstIrreducibleSourceResidualExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.LiTorrMicroscopicToBulkGravitomagneticSumBidiExact as Micro
import DASHI.Physics.ExoticGravity.AntigravityJointProofSearchFrontierExact as Joint
import DASHI.Physics.ExoticGravity.AntigravityConstraintPruningVsBundlePaymentExact as Pruning
import DASHI.Law.SensibLawProofDirectedSearchIntentExact as Search

currentJointBundleIsSourceGeometry :
  Joint.currentRecommendedBundle ≡ Joint.sourceGeometryBundle
currentJointBundleIsSourceGeometry = refl

currentLiteralGeometryFirstOpen :
  Geometry.currentFirstOpenGeometryLeaf ≡ Geometry.sourceShapeLeaf
currentLiteralGeometryFirstOpen = refl

currentMicroscopicBulkFirstOpen :
  Micro.currentFirstOpenMicroscopicBulkLeaf ≡ Micro.sourceDistributionLeaf
currentMicroscopicBulkFirstOpen = refl

data IrreducibleSourceCoordinate : Set where
  literalSourceShape : IrreducibleSourceCoordinate
  physicalSourceDistribution : IrreducibleSourceCoordinate
  sourceMassCurrent : IrreducibleSourceCoordinate
  sourceStressEnergy : IrreducibleSourceCoordinate
  probeGeometry : IrreducibleSourceCoordinate

record SourceAcquisitionTarget : Set where
  constructor source-acquisition-target
  field
    apparatusCarrier : String
    exactShapeCarrier : String
    sourceDistributionCarrier : String
    massCurrentCarrier : String
    stressEnergyCarrier : String
    probeGeometryCarrier : String
    calibrationRevision : String
    sameApparatusIdentityCarrier : String

open SourceAcquisitionTarget public

data CurrentSourceAcquisitionAuthority : Set where

noCurrentCanonicalSourceAcquisitionTarget :
  CurrentSourceAcquisitionAuthority → SourceAcquisitionTarget
noCurrentCanonicalSourceAcquisitionTarget ()

data SourceResidual : Set where
  missingLiteralSourceShape : SourceResidual
  missingPhysicalSourceDistribution : SourceResidual
  missingMassCurrentMeasurement : SourceResidual
  missingStressEnergyReconstruction : SourceResidual
  missingProbeGeometry : SourceResidual
  missingSameApparatusIdentity : SourceResidual

producerForSourceResidual : SourceResidual → Search.ProducerClass
producerForSourceResidual missingLiteralSourceShape = Search.empiricalEvidenceProducer
producerForSourceResidual missingPhysicalSourceDistribution = Search.empiricalEvidenceProducer
producerForSourceResidual missingMassCurrentMeasurement = Search.empiricalEvidenceProducer
producerForSourceResidual missingStressEnergyReconstruction = Search.empiricalEvidenceProducer
producerForSourceResidual missingProbeGeometry = Search.empiricalEvidenceProducer
producerForSourceResidual missingSameApparatusIdentity = Search.identityProducer

record FirstIrreducibleSourceBoundary : Set where
  constructor first-irreducible-source-boundary
  field
    sourceShapeEqualsSourceDistribution : Bool
    illustrativeHistoricalVolumePaysLiteralShape : Bool
    literatureIonCountPaysActualSourceDistribution : Bool
    heterogeneousLegacyConstraintsPaySameApparatusSource : Bool
    currentJointFrontierRequiresSourceFacingAcquisition : Bool
    sameApparatusIdentityRequired : Bool
    completedSourceTargetAutomaticallyProvesAntigravity : Bool

canonicalFirstIrreducibleSourceBoundary : FirstIrreducibleSourceBoundary
canonicalFirstIrreducibleSourceBoundary =
  first-irreducible-source-boundary false false false false true true false
