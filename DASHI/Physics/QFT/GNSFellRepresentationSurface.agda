module DASHI.Physics.QFT.GNSFellRepresentationSurface where

open import Agda.Primitive using (Setω)
open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.String using (String)
open import Data.Empty using (⊥)
open import Data.List.Base using (List; _∷_; [])

import DASHI.Physics.QFT.AQFTTypedNetSurface as AQFT
import DASHI.Physics.QFT.DHRGaugeReceiptSurface as DHR
import DASHI.Physics.QFT.ModularTheoryReceiptSurface as Modular

------------------------------------------------------------------------
-- GNS/Fell representation target surface.
--
-- This module records the representation-theoretic targets between the
-- AQFT local-algebra surface, the modular-theory receipt surface, and the DHR
-- gauge reconstruction surface:
--
--   * GNS universal property,
--   * state/observable duality,
--   * folia of representations,
--   * superselection sectors as representation classes,
--   * Fell topology over representation classes,
--   * KMS family proximity.
--
-- It does not construct a Hilbert representation, state space, folium,
-- superselection classification, Fell topology, KMS convergence theorem,
-- interacting AQFT, Standard Model, or GRQFT promotion receipt.

postulate
  Observable :
    AQFT.Region →
    Set

  State :
    AQFT.Region →
    Set

  Representation :
    AQFT.Region →
    Set

  RepresentationIntertwiner :
    {region : AQFT.Region} →
    Representation region →
    Representation region →
    Set

  RepresentationClass :
    AQFT.Region →
    Set

  Folium :
    (region : AQFT.Region) →
    Representation region →
    Set

  FellNeighbourhood :
    (region : AQFT.Region) →
    RepresentationClass region →
    Set

  KMSFamily :
    AQFT.Region →
    Set

  KMSProximity :
    (region : AQFT.Region) →
    KMSFamily region →
    KMSFamily region →
    Set

data GNSFellRepresentationStatus : Set where
  gnsFellTargetsOnlyNoPromotion :
    GNSFellRepresentationStatus

data GNSFellOpenObligation : Set where
  missingGNSUniversalProperty :
    GNSFellOpenObligation

  missingStateObservableDuality :
    GNSFellOpenObligation

  missingFoliumConstruction :
    GNSFellOpenObligation

  missingSuperselectionRepresentationClasses :
    GNSFellOpenObligation

  missingFellTopology :
    GNSFellOpenObligation

  missingKMSFamilyProximity :
    GNSFellOpenObligation

  missingDHRCompatibility :
    GNSFellOpenObligation

  missingGRQFTAuthority :
    GNSFellOpenObligation

canonicalGNSFellOpenObligations :
  List GNSFellOpenObligation
canonicalGNSFellOpenObligations =
  missingGNSUniversalProperty
  ∷ missingStateObservableDuality
  ∷ missingFoliumConstruction
  ∷ missingSuperselectionRepresentationClasses
  ∷ missingFellTopology
  ∷ missingKMSFamilyProximity
  ∷ missingDHRCompatibility
  ∷ missingGRQFTAuthority
  ∷ []

data GNSFellPromotionAuthorityToken : Set where

record GNSUniversalPropertyTarget : Setω where
  field
    modularGNSSurface :
      Modular.GNSVonNeumannClosureSurface

    region :
      AQFT.Region

    selectedState :
      State region

    cyclicRepresentation :
      Representation region

    universalArrowTarget :
      (candidate : Representation region) →
      Set

    statePreservationTarget :
      (candidate : Representation region) →
      Set

    uniquenessUpToUnitaryTarget :
      (candidate : Representation region) →
      Set

    universalPropertyProved :
      Bool

    universalPropertyProvedIsFalse :
      universalPropertyProved ≡ false

    gnsUniversalBoundary :
      List String

open GNSUniversalPropertyTarget public

record StateObservableDualityTarget : Setω where
  field
    region :
      AQFT.Region

    stateSpace :
      State region →
      Set

    observableSpace :
      Observable region →
      Set

    evaluationPairing :
      State region →
      Observable region →
      Set

    statesSeparateObservablesTarget :
      Set

    observablesSeparateStatesTarget :
      Set

    dualityProved :
      Bool

    dualityProvedIsFalse :
      dualityProved ≡ false

    dualityBoundary :
      List String

open StateObservableDualityTarget public

record FoliumTarget : Setω where
  field
    region :
      AQFT.Region

    baseRepresentation :
      Representation region

    folium :
      Folium region baseRepresentation

    normalStateTarget :
      State region →
      Set

    quasiEquivalenceTarget :
      Representation region →
      Representation region →
      Set

    foliumMembershipTarget :
      State region →
      Set

    foliumConstructed :
      Bool

    foliumConstructedIsFalse :
      foliumConstructed ≡ false

    foliumBoundary :
      List String

open FoliumTarget public

record SuperselectionRepresentationClassTarget : Setω where
  field
    dhrSelectionTarget :
      DHR.DHRSelectionCriterionTarget

    region :
      AQFT.Region

    sector :
      DHR.SuperselectionSector

    representationClass :
      RepresentationClass region

    sectorToRepresentationClassTarget :
      DHR.SuperselectionSector →
      RepresentationClass region →
      Set

    disjointnessTarget :
      RepresentationClass region →
      RepresentationClass region →
      Set

    sectorClassificationProved :
      Bool

    sectorClassificationProvedIsFalse :
      sectorClassificationProved ≡ false

    sectorBoundary :
      List String

open SuperselectionRepresentationClassTarget public

record FellTopologyTarget : Setω where
  field
    region :
      AQFT.Region

    representationClass :
      RepresentationClass region

    fellNeighbourhood :
      FellNeighbourhood region representationClass

    weakContainmentTarget :
      RepresentationClass region →
      RepresentationClass region →
      Set

    matrixCoefficientApproximationTarget :
      RepresentationClass region →
      RepresentationClass region →
      Set

    sectorClosureTarget :
      RepresentationClass region →
      Set

    fellTopologyConstructed :
      Bool

    fellTopologyConstructedIsFalse :
      fellTopologyConstructed ≡ false

    fellBoundary :
      List String

open FellTopologyTarget public

record KMSFamilyProximityTarget : Setω where
  field
    modularReceipt :
      Modular.KMSConditionReceiptTarget

    region :
      AQFT.Region

    kmsFamily :
      KMSFamily region

    referenceKMSFamily :
      KMSFamily region

    proximity :
      KMSProximity region kmsFamily referenceKMSFamily

    fellCompatibilityTarget :
      FellTopologyTarget →
      Set

    temperatureParameterTarget :
      Set

    kmsProximityProved :
      Bool

    kmsProximityProvedIsFalse :
      kmsProximityProved ≡ false

    kmsProximityBoundary :
      List String

open KMSFamilyProximityTarget public

postulate
  abstractRegion :
    AQFT.Region

  abstractState :
    State abstractRegion

  abstractObservable :
    Observable abstractRegion

  abstractRepresentation :
    Representation abstractRegion

  abstractRepresentationClass :
    RepresentationClass abstractRegion

  abstractFolium :
    Folium abstractRegion abstractRepresentation

  abstractFellNeighbourhood :
    FellNeighbourhood abstractRegion abstractRepresentationClass

  abstractKMSFamily :
    KMSFamily abstractRegion

  abstractReferenceKMSFamily :
    KMSFamily abstractRegion

  abstractKMSProximity :
    KMSProximity
      abstractRegion
      abstractKMSFamily
      abstractReferenceKMSFamily

  abstractSuperselectionSector :
    DHR.SuperselectionSector

  abstractUniversalArrowTarget :
    (candidate : Representation abstractRegion) →
    Set

  abstractStatePreservationTarget :
    (candidate : Representation abstractRegion) →
    Set

  abstractUniquenessUpToUnitaryTarget :
    (candidate : Representation abstractRegion) →
    Set

  abstractStateSpace :
    State abstractRegion →
    Set

  abstractObservableSpace :
    Observable abstractRegion →
    Set

  abstractEvaluationPairing :
    State abstractRegion →
    Observable abstractRegion →
    Set

  abstractStatesSeparateObservablesTarget :
    Set

  abstractObservablesSeparateStatesTarget :
    Set

  abstractNormalStateTarget :
    State abstractRegion →
    Set

  abstractQuasiEquivalenceTarget :
    Representation abstractRegion →
    Representation abstractRegion →
    Set

  abstractFoliumMembershipTarget :
    State abstractRegion →
    Set

  abstractSectorToRepresentationClassTarget :
    DHR.SuperselectionSector →
    RepresentationClass abstractRegion →
    Set

  abstractDisjointnessTarget :
    RepresentationClass abstractRegion →
    RepresentationClass abstractRegion →
    Set

  abstractWeakContainmentTarget :
    RepresentationClass abstractRegion →
    RepresentationClass abstractRegion →
    Set

  abstractMatrixCoefficientApproximationTarget :
    RepresentationClass abstractRegion →
    RepresentationClass abstractRegion →
    Set

  abstractSectorClosureTarget :
    RepresentationClass abstractRegion →
    Set

  abstractFellCompatibilityTarget :
    FellTopologyTarget →
    Set

  abstractTemperatureParameterTarget :
    Set

canonicalGNSUniversalPropertyTarget :
  GNSUniversalPropertyTarget
canonicalGNSUniversalPropertyTarget =
  record
    { modularGNSSurface =
        Modular.canonicalGNSVonNeumannClosureSurface
    ; region =
        abstractRegion
    ; selectedState =
        abstractState
    ; cyclicRepresentation =
        abstractRepresentation
    ; universalArrowTarget =
        abstractUniversalArrowTarget
    ; statePreservationTarget =
        abstractStatePreservationTarget
    ; uniquenessUpToUnitaryTarget =
        abstractUniquenessUpToUnitaryTarget
    ; universalPropertyProved =
        false
    ; universalPropertyProvedIsFalse =
        refl
    ; gnsUniversalBoundary =
        "GNS universal property is recorded as a target for a selected state and cyclic representation"
        ∷ "universal arrows, state preservation, and uniqueness up to unitary equivalence remain open"
        ∷ []
    }

canonicalStateObservableDualityTarget :
  StateObservableDualityTarget
canonicalStateObservableDualityTarget =
  record
    { region =
        abstractRegion
    ; stateSpace =
        abstractStateSpace
    ; observableSpace =
        abstractObservableSpace
    ; evaluationPairing =
        abstractEvaluationPairing
    ; statesSeparateObservablesTarget =
        abstractStatesSeparateObservablesTarget
    ; observablesSeparateStatesTarget =
        abstractObservablesSeparateStatesTarget
    ; dualityProved =
        false
    ; dualityProvedIsFalse =
        refl
    ; dualityBoundary =
        "State-observable duality is an evaluation/separation target only"
        ∷ "no Born-rule probability theorem or empirical measurement map is constructed here"
        ∷ []
    }

canonicalFoliumTarget :
  FoliumTarget
canonicalFoliumTarget =
  record
    { region =
        abstractRegion
    ; baseRepresentation =
        abstractRepresentation
    ; folium =
        abstractFolium
    ; normalStateTarget =
        abstractNormalStateTarget
    ; quasiEquivalenceTarget =
        abstractQuasiEquivalenceTarget
    ; foliumMembershipTarget =
        abstractFoliumMembershipTarget
    ; foliumConstructed =
        false
    ; foliumConstructedIsFalse =
        refl
    ; foliumBoundary =
        "Folium is a target for normal states attached to a representation class"
        ∷ "quasi-equivalence and folium membership are not proved here"
        ∷ []
    }

canonicalSuperselectionRepresentationClassTarget :
  SuperselectionRepresentationClassTarget
canonicalSuperselectionRepresentationClassTarget =
  record
    { dhrSelectionTarget =
        DHR.canonicalDHRSelectionCriterionTarget
    ; region =
        abstractRegion
    ; sector =
        abstractSuperselectionSector
    ; representationClass =
        abstractRepresentationClass
    ; sectorToRepresentationClassTarget =
        abstractSectorToRepresentationClassTarget
    ; disjointnessTarget =
        abstractDisjointnessTarget
    ; sectorClassificationProved =
        false
    ; sectorClassificationProvedIsFalse =
        refl
    ; sectorBoundary =
        "Superselection sectors are staged as representation-class targets"
        ∷ "DHR localization, transportability, statistics, and disjointness remain open"
        ∷ []
    }

canonicalFellTopologyTarget :
  FellTopologyTarget
canonicalFellTopologyTarget =
  record
    { region =
        abstractRegion
    ; representationClass =
        abstractRepresentationClass
    ; fellNeighbourhood =
        abstractFellNeighbourhood
    ; weakContainmentTarget =
        abstractWeakContainmentTarget
    ; matrixCoefficientApproximationTarget =
        abstractMatrixCoefficientApproximationTarget
    ; sectorClosureTarget =
        abstractSectorClosureTarget
    ; fellTopologyConstructed =
        false
    ; fellTopologyConstructedIsFalse =
        refl
    ; fellBoundary =
        "Fell topology is a target over representation classes"
        ∷ "weak containment, matrix-coefficient approximation, and sector closure are not constructed here"
        ∷ []
    }

canonicalKMSFamilyProximityTarget :
  KMSFamilyProximityTarget
canonicalKMSFamilyProximityTarget =
  record
    { modularReceipt =
        Modular.canonicalKMSConditionReceiptTarget
    ; region =
        abstractRegion
    ; kmsFamily =
        abstractKMSFamily
    ; referenceKMSFamily =
        abstractReferenceKMSFamily
    ; proximity =
        abstractKMSProximity
    ; fellCompatibilityTarget =
        abstractFellCompatibilityTarget
    ; temperatureParameterTarget =
        abstractTemperatureParameterTarget
    ; kmsProximityProved =
        false
    ; kmsProximityProvedIsFalse =
        refl
    ; kmsProximityBoundary =
        "KMS family proximity is a Fell/modular comparison target only"
        ∷ "temperature parameters, analytic KMS data, and Fell compatibility remain open"
        ∷ []
    }

record GNSFellRepresentationSurface : Setω where
  field
    status :
      GNSFellRepresentationStatus

    typedNetSurface :
      AQFT.AQFTTypedNetSurface

    modularTheorySurface :
      Modular.ModularTheoryReceiptSurface

    dhrGaugeSurface :
      DHR.DHRGaugeReceiptSurface

    gnsUniversalPropertyTarget :
      GNSUniversalPropertyTarget

    stateObservableDualityTarget :
      StateObservableDualityTarget

    foliumTarget :
      FoliumTarget

    superselectionRepresentationClassTarget :
      SuperselectionRepresentationClassTarget

    fellTopologyTarget :
      FellTopologyTarget

    kmsFamilyProximityTarget :
      KMSFamilyProximityTarget

    openObligations :
      List GNSFellOpenObligation

    openObligationsAreCanonical :
      openObligations ≡ canonicalGNSFellOpenObligations

    gnsFellPromoted :
      Bool

    gnsFellPromotedIsFalse :
      gnsFellPromoted ≡ false

    noPromotionWithoutAuthority :
      GNSFellPromotionAuthorityToken →
      ⊥

    receiptBoundary :
      List String

open GNSFellRepresentationSurface public

canonicalGNSFellRepresentationSurface :
  GNSFellRepresentationSurface
canonicalGNSFellRepresentationSurface =
  record
    { status =
        gnsFellTargetsOnlyNoPromotion
    ; typedNetSurface =
        AQFT.canonicalAQFTTypedNetSurface
    ; modularTheorySurface =
        Modular.canonicalModularTheoryReceiptSurface
    ; dhrGaugeSurface =
        DHR.canonicalDHRGaugeReceiptSurface
    ; gnsUniversalPropertyTarget =
        canonicalGNSUniversalPropertyTarget
    ; stateObservableDualityTarget =
        canonicalStateObservableDualityTarget
    ; foliumTarget =
        canonicalFoliumTarget
    ; superselectionRepresentationClassTarget =
        canonicalSuperselectionRepresentationClassTarget
    ; fellTopologyTarget =
        canonicalFellTopologyTarget
    ; kmsFamilyProximityTarget =
        canonicalKMSFamilyProximityTarget
    ; openObligations =
        canonicalGNSFellOpenObligations
    ; openObligationsAreCanonical =
        refl
    ; gnsFellPromoted =
        false
    ; gnsFellPromotedIsFalse =
        refl
    ; noPromotionWithoutAuthority =
        λ ()
    ; receiptBoundary =
        "GNS/FellRepresentationSurface records representation-theoretic targets only"
        ∷ "GNS universal property, state-observable duality, folia, superselection representation classes, Fell topology, and KMS family proximity remain open"
        ∷ "This surface imports modular and DHR target surfaces but does not construct their missing representation or gauge data"
        ∷ "No vacuum selection, Born-rule theorem, interacting AQFT, Standard Model, GRQFT, or TOE promotion follows from this surface"
        ∷ []
    }
