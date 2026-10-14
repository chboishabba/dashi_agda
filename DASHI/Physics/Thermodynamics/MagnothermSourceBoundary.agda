module DASHI.Physics.Thermodynamics.MagnothermSourceBoundary where

open import Agda.Builtin.String using (String)
open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator
open import DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem

------------------------------------------------------------------------
-- MAGNOTHERM acquisition / attribution boundary.
--
-- This module records what the external sources say and how strongly the
-- repository may use those statements.  It intentionally does not turn
-- source text into a proof of calibrated system performance.
------------------------------------------------------------------------

data SourceClass : Set where
  peerReviewedOpenAccess : SourceClass
  vendorTechnologyPage   : SourceClass
  vendorDevelopmentPage  : SourceClass

record SourceRef : Set where
  constructor sourceRef
  field
    title      : String
    locator    : String
    accessed   : String
    sourceClass : SourceClass

stableOperationSource : SourceRef
stableOperationSource = sourceRef
  "Stable Operation of Copper-Protected La(FeMnSi)13Hy Regenerators in a Magnetic Cooling Unit"
  "doi:10.1021/acsaenm.4c00747; PMCID:PMC11773641"
  "2026-10-14"
  peerReviewedOpenAccess

magnothermTechnologySource : SourceRef
magnothermTechnologySource = sourceRef
  "MAGNOTHERM Technology"
  "https://www.magnotherm.com/technology"
  "2026-10-14"
  vendorTechnologyPage

magnothermStellarSource : SourceRef
magnothermStellarSource = sourceRef
  "MAGNOTHERM STELLAR"
  "https://www.magnotherm.com/stellar"
  "2026-10-14"
  vendorDevelopmentPage

record PeerReviewedMagnothermObservations : Set₁ where
  field
    laFeMnSiHydrogenatedRegenerator : Set
    copperCoatingApplied            : Set
    inhibitorAugmentedAqueousMedium : Set
    bidirectionalFlushingUsed       : Set
    repeatedMagnetisationUsed       : Set
    unprotectedCorrosionObserved    : Set
    nearChannelCloggingObserved     : Set
    protectedSurfacePreserved       : Set
    coatingAccommodatesBreathing    : Set
    oneTeslaAdiabaticChangeMeasured : Set

record VendorTechnologyObservations : Set₁ where
  field
    usesLaFeSiFamily              : Set
    roomTemperatureUsesPermanentMagnets : Set
    transferMediumWaterAlcohol    : Set
    transferRunsThroughPorousMaterial : Set
    AMRSynchronisesFieldAndFlow   : Set
    rotationalWorkRecoveryClaimed : Set
    efficiencyIncreaseUpTo30PercentClaimed : Set

record StellarDevelopmentObservations : Set₁ where
  field
    superconductingFieldArchitecture : Set
    targetFieldFiveTesla              : Set
    moduleVisionAtLeast125kW           : Set
    notYetCommerciallyAvailable       : Set

------------------------------------------------------------------------
-- Promotion policy.
------------------------------------------------------------------------

data EvidenceLevel : Set where
  sourcedObservation : EvidenceLevel
  calibratedComponent : EvidenceLevel
  calibratedDevice    : EvidenceLevel
  theoremAuthority    : EvidenceLevel

record MagnothermPromotionBoundary : Set₁ where
  field
    peerReviewedObservationLevel : EvidenceLevel
    vendorObservationLevel       : EvidenceLevel

    sameDeviceCalibrationRequiredForCOP : Set
    sameDeviceCalibrationRequiredForCapacity : Set
    qualifiedAgingIntervalIsNotLifetime : Set
    vendorEfficiencyClaimNotPromoted    : Set
    stellarCapacityVisionNotPromoted    : Set
    sourceObservationDoesNotInstantiateValidSystem : Set

------------------------------------------------------------------------
-- Crosswalk: an acquired observation may constrain a generic model, but
-- model validity still requires the generic proof-carrying interfaces.
------------------------------------------------------------------------

record MagnothermModelCrosswalk
  (M : MagnetocaloricMaterial)
  (G : RegeneratorGeometry)
  (F : TransferMedium) : Set₁ where
  field
    MaterialIdentification : Set
    GeometryIdentification : Set
    MediumIdentification   : Set
    materialIdentification : MaterialIdentification
    geometryIdentification : GeometryIdentification
    mediumIdentification   : MediumIdentification
