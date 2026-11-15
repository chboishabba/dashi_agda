module DASHI.Physics.Thermodynamics.MagnothermSourceBoundary where

open import DASHI.Core.Prelude
import DASHI.Core.AttributedSourceCore as Source
import DASHI.Physics.Thermodynamics.MagnothermAttributedEvidenceExact as Attribution

open import DASHI.Physics.Thermodynamics.MagnetocaloricMaterial
open import DASHI.Physics.Thermodynamics.CaloricRegenerator
open import DASHI.Physics.Thermodynamics.ActiveMagneticRegenerator
open import DASHI.Physics.Thermodynamics.ProtectedMagnetocaloricSystem

------------------------------------------------------------------------
-- MAGNOTHERM acquisition / attribution boundary.
--
-- Canonical attribution is owned by MagnothermAttributedEvidenceExact using
-- DASHI.Core.AttributedSourceCore.  This module owns the domain-facing claim
-- ceiling and generic-model crosswalk.  Source identity, access carrier,
-- scientific authority, same-object status and DASHI reconstruction remain
-- distinct throughout.
------------------------------------------------------------------------

stableOperationSource : Source.AttributedSource
stableOperationSource = Attribution.stableOperationArticle

magnothermTechnologySource : Source.AttributedSource
magnothermTechnologySource = Attribution.magnothermTechnologyPage

magnothermStellarSource : Source.AttributedSource
magnothermStellarSource = Attribution.magnothermStellarPage

magnothermSourceAtlas : Source.AttributedSourceAtlas
magnothermSourceAtlas = Attribution.magnothermAttributedSourceAtlas

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

    -- Claim-relative aging payments from the 2025 paper.
    sixWeekContinuedOperationObserved : Set
    threeMonthMicrochannelPreliminaryObserved : Set
    monthsToYearsLongTermExperimentCompleted : Bool
    monthsToYearsLongTermExperimentCompletedIsFalse :
      monthsToYearsLongTermExperimentCompleted ≡ false

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
    twoModule250kWDepictionClaimed     : Set
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
    preliminaryThreeMonthObservationIsNotLifetime : Set
    plannedLongTermExperimentIsNotCompletedEvidence : Set
    vendorEfficiencyClaimNotPromoted    : Set
    stellarFieldTargetNotPromoted       : Set
    stellarCapacityVisionNotPromoted    : Set
    sourceObservationDoesNotInstantiateValidSystem : Set

    canonicalAttributedSourceRequired : Set
    primarynessIsClaimRelative : Set
    accessCarrierDoesNotCreateAuthorshipOrAuthority : Set
    sourceClaimDoesNotTransferAuthorshipToDASHI : Set

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
    SameObjectEvidence     : Set
    ClaimRoleCompatible    : Set

    materialIdentification : MaterialIdentification
    geometryIdentification : GeometryIdentification
    mediumIdentification   : MediumIdentification
    sameObjectEvidence     : SameObjectEvidence
    claimRoleCompatible    : ClaimRoleCompatible
