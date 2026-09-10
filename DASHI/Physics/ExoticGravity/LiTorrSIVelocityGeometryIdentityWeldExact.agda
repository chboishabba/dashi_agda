module DASHI.Physics.ExoticGravity.LiTorrSIVelocityGeometryIdentityWeldExact where

open import DASHI.Core.Prelude
open import Agda.Builtin.Bool using (Bool; false; true)
open import Agda.Builtin.String using (String)

import DASHI.Physics.Units.SI as SI
import DASHI.Physics.ExoticGravity.LiTorrComponentResolvedMassCurrentReverseSearchExact as Source
import DASHI.Physics.ExoticGravity.LiTorrGeometryAcquisitionBidiExact as Geometry
import DASHI.Physics.ExoticGravity.MaterialEffectiveNegativeGSIMetrologyBridgeExact as SIM
import DASHI.Physics.ExoticGravity.SuperconductingChargeMassCurrentBidiExact as Current

------------------------------------------------------------------------
-- LI-TORR SAME-OBJECT SI VELOCITY / GEOMETRY WELD
--
-- A component velocity is only useful for J_m when it belongs to the same
-- apparatus, phase state, drive revision and spatial geometry used by the
-- downstream mass-current and stress-energy reconstruction.
------------------------------------------------------------------------

record SIApparatusIdentity : Set where
  constructor si-apparatus-identity
  field
    apparatusRevision : String
    sampleRevision : String
    geometryRevision : String
    driveRevision : String
    phaseStateRevision : String
    probeRevision : String

open SIApparatusIdentity public

record SIVelocityGeometryReceipt : Set where
  constructor si-velocity-geometry-receipt
  field
    identity : SIApparatusIdentity
    component : Source.SourceComponent
    componentVelocity : SI.Measurement SI.Velocity SI.unitScale
    characteristicRadius : SI.Measurement SI.Length SI.unitScale
    probeDistance : SI.Measurement SI.Length SI.unitScale
    angularFrequency : SI.Measurement SI.Frequency SI.unitScale
    sourceShapeLocator : String
    spatialDistributionLocator : String
    coherenceStateLocator : String
    sameApparatus : Bool
    sameDriveRevision : Bool
    samePhaseState : Bool
    sameGeometryRevision : Bool

open SIVelocityGeometryReceipt public

record SIJmEligibilityReceipt : Set where
  constructor si-jm-eligibility-receipt
  field
    sourceMeasurement : SIM.SIComponentSourceMeasurement
    velocityGeometry : SIVelocityGeometryReceipt
    sourceAndGeometrySameRevision : Bool
    componentIdentityMatches : Bool
    spatialDistributionBound : Bool
    eligibleForMassCurrentDerivation : Bool

open SIJmEligibilityReceipt public

------------------------------------------------------------------------
-- Cross-weld to the pre-existing geometry and mass-current frontiers.
------------------------------------------------------------------------

geometryStillOpenAtSourceShape :
  Geometry.currentFirstOpenGeometryLeaf ≡ Geometry.sourceShapeLeaf
geometryStillOpenAtSourceShape = refl

velocityRemainsCurrentComponentResidual :
  Source.currentResidual ≡ Current.missingComponentVelocity
velocityRemainsCurrentComponentResidual = refl

record LiTorrSIVelocityGeometryBoundary : Set where
  constructor li-torr-si-velocity-geometry-boundary
  field
    genericVelocityMayPayExactApparatusVelocity : Bool
    genericRadiusMayPayExactSourceShape : Bool
    sameMaterialNameImpliesSamePhaseState : Bool
    sameNominalDriveImpliesSameWaveformRevision : Bool
    sameObjectIdentityRequiredForJm : Bool
    siUnitsReplaceCarrierProvenance : Bool
    closedVelocityGeometryAutomaticallyProvesAnomaly : Bool

canonicalLiTorrSIVelocityGeometryBoundary :
  LiTorrSIVelocityGeometryBoundary
canonicalLiTorrSIVelocityGeometryBoundary =
  li-torr-si-velocity-geometry-boundary
    false false false false true false false
