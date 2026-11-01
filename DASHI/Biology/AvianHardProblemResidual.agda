module DASHI.Biology.AvianHardProblemResidual where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.AvianCompassSurface

------------------------------------------------------------------------
-- Finite location lattice for the avian hard-problem residual.
------------------------------------------------------------------------

data HardProblemResidualLocation : Set where
  physicalSpinGeometry : HardProblemResidualLocation
  retinalActivationGeometry : HardProblemResidualLocation
  visualOverlayQuotient : HardProblemResidualLocation
  orientationBehaviorReceipt : HardProblemResidualLocation
  phenomenalContentGap : HardProblemResidualLocation

data PromotionStatus : Set where
  promotedObservable : PromotionStatus
  quotientedObservable : PromotionStatus
  blockedPhenomenal : PromotionStatus

data MissingPromotion : Set where
  noFirstPersonOverlayContentCarrier : MissingPromotion
  noPhenomenalIdentityMapFromOverlayQuotient : MissingPromotion
  noZombieExclusionFromBehaviorReceipt : MissingPromotion
  noConsciousnessClosureRule : MissingPromotion

observableResidualLocations : List HardProblemResidualLocation
observableResidualLocations =
  physicalSpinGeometry
  ∷ retinalActivationGeometry
  ∷ visualOverlayQuotient
  ∷ orientationBehaviorReceipt
  ∷ []

blockedResidualLocations : List HardProblemResidualLocation
blockedResidualLocations =
  phenomenalContentGap ∷ []

allResidualLocations : List HardProblemResidualLocation
allResidualLocations =
  physicalSpinGeometry
  ∷ retinalActivationGeometry
  ∷ visualOverlayQuotient
  ∷ orientationBehaviorReceipt
  ∷ phenomenalContentGap
  ∷ []

residualStatus :
  HardProblemResidualLocation →
  PromotionStatus
residualStatus physicalSpinGeometry = promotedObservable
residualStatus retinalActivationGeometry = promotedObservable
residualStatus visualOverlayQuotient = quotientedObservable
residualStatus orientationBehaviorReceipt = promotedObservable
residualStatus phenomenalContentGap = blockedPhenomenal

gapPromotions :
  HardProblemResidualLocation →
  List MissingPromotion
gapPromotions physicalSpinGeometry = []
gapPromotions retinalActivationGeometry = []
gapPromotions visualOverlayQuotient =
  noFirstPersonOverlayContentCarrier
  ∷ noPhenomenalIdentityMapFromOverlayQuotient
  ∷ []
gapPromotions orientationBehaviorReceipt =
  noZombieExclusionFromBehaviorReceipt
  ∷ []
gapPromotions phenomenalContentGap =
  noFirstPersonOverlayContentCarrier
  ∷ noPhenomenalIdentityMapFromOverlayQuotient
  ∷ noZombieExclusionFromBehaviorReceipt
  ∷ noConsciousnessClosureRule
  ∷ []

exactMissingPhenomenalPromotion : List MissingPromotion
exactMissingPhenomenalPromotion =
  gapPromotions phenomenalContentGap

------------------------------------------------------------------------
-- Chain certificates.
------------------------------------------------------------------------

record AvianHardProblemResidualCertificate
    (receipt : AvianCompassBridgeReceipt) : Set₁ where
  field
    surface : AvianCompassSurface
    surfaceMatchesReceipt :
      surface ≡ AvianCompassBridgeReceipt.surface receipt

    promotedChain : List HardProblemResidualLocation
    promotedChainIsObservable :
      promotedChain ≡ observableResidualLocations

    blockedChain : List HardProblemResidualLocation
    blockedChainIsPhenomenal :
      blockedChain ≡ blockedResidualLocations

    bridgeChainCarried : List BridgeLayer
    bridgeChainCarriedMatchesReceipt :
      bridgeChainCarried ≡ bridgeChain receipt

    overlayGeometriesCarried : List PerceptualGeometry
    overlayGeometriesCarriedMatchesReceipt :
      overlayGeometriesCarried ≡ perceptualGeometries receipt

    physicalFunctionalOverlayPromoted : Bool
    physicalFunctionalOverlayPromotedIsTrue :
      physicalFunctionalOverlayPromoted ≡ true

    formalOverlayConstrained : Bool
    formalOverlayConstrainedIsTrue :
      formalOverlayConstrained ≡ true

    phenomenalContentRecovered : Bool
    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    zombieArgumentClosed : Bool
    zombieArgumentClosedIsFalse :
      zombieArgumentClosed ≡ false

    consciousnessClosure : Bool
    consciousnessClosureIsFalse :
      consciousnessClosure ≡ false

    observablePromotionInherited :
      promotedBiologicalObservable receipt ≡ true

    phenomenalBlockInherited :
      subjectiveQualiaRecovered receipt ≡ false

    residualGapLocation : HardProblemResidualLocation
    residualGapLocationIsPhenomenal :
      residualGapLocation ≡ phenomenalContentGap

    residualGapStatus : PromotionStatus
    residualGapStatusIsBlocked :
      residualGapStatus ≡ blockedPhenomenal

    missingPromotion : List MissingPromotion
    missingPromotionIsExact :
      missingPromotion ≡ exactMissingPhenomenalPromotion

    boundaryReading : String

open AvianHardProblemResidualCertificate public

record AvianSurfaceHardProblemBoundary
    (surface : AvianCompassSurface) : Set₁ where
  field
    promotablePhysicalFunctionalOverlay :
      List HardProblemResidualLocation

    promotablePhysicalFunctionalOverlayIsObservable :
      promotablePhysicalFunctionalOverlay ≡ observableResidualLocations

    blockedPhenomenalOverlay :
      HardProblemResidualLocation

    blockedPhenomenalOverlayIsGap :
      blockedPhenomenalOverlay ≡ phenomenalContentGap

    formalOverlayConstrained : Bool
    formalOverlayConstrainedIsTrue :
      formalOverlayConstrained ≡ true

    phenomenalContentRecovered : Bool
    phenomenalContentRecoveredIsFalse :
      phenomenalContentRecovered ≡ false

    consciousnessClosure : Bool
    consciousnessClosureIsFalse :
      consciousnessClosure ≡ false

    missingPromotion : List MissingPromotion
    missingPromotionIsExact :
      missingPromotion ≡ exactMissingPhenomenalPromotion

    surfaceBoundaryReading : String

open AvianSurfaceHardProblemBoundary public

------------------------------------------------------------------------
-- Canonical helpers.
------------------------------------------------------------------------

avianSurfaceHardProblemBoundary :
  (surface : AvianCompassSurface) →
  AvianSurfaceHardProblemBoundary surface
avianSurfaceHardProblemBoundary surface =
  record
    { promotablePhysicalFunctionalOverlay = observableResidualLocations
    ; promotablePhysicalFunctionalOverlayIsObservable = refl
    ; blockedPhenomenalOverlay = phenomenalContentGap
    ; blockedPhenomenalOverlayIsGap = refl
    ; formalOverlayConstrained = true
    ; formalOverlayConstrainedIsTrue = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; consciousnessClosure = false
    ; consciousnessClosureIsFalse = refl
    ; missingPromotion = exactMissingPhenomenalPromotion
    ; missingPromotionIsExact = refl
    ; surfaceBoundaryReading =
        "The avian compass surface constrains spin-to-retina overlay geometry, but does not promote first-person overlay content."
    }

avianBridgeHardProblemResidual :
  (receipt : AvianCompassBridgeReceipt) →
  AvianHardProblemResidualCertificate receipt
avianBridgeHardProblemResidual receipt =
  record
    { surface = AvianCompassBridgeReceipt.surface receipt
    ; surfaceMatchesReceipt = refl
    ; promotedChain = observableResidualLocations
    ; promotedChainIsObservable = refl
    ; blockedChain = blockedResidualLocations
    ; blockedChainIsPhenomenal = refl
    ; bridgeChainCarried = bridgeChain receipt
    ; bridgeChainCarriedMatchesReceipt = refl
    ; overlayGeometriesCarried = perceptualGeometries receipt
    ; overlayGeometriesCarriedMatchesReceipt = refl
    ; physicalFunctionalOverlayPromoted = true
    ; physicalFunctionalOverlayPromotedIsTrue = refl
    ; formalOverlayConstrained = true
    ; formalOverlayConstrainedIsTrue = refl
    ; phenomenalContentRecovered = false
    ; phenomenalContentRecoveredIsFalse = refl
    ; zombieArgumentClosed = false
    ; zombieArgumentClosedIsFalse = refl
    ; consciousnessClosure = false
    ; consciousnessClosureIsFalse = refl
    ; observablePromotionInherited =
        promotedBiologicalObservableIsTrue receipt
    ; phenomenalBlockInherited =
        subjectiveQualiaRecoveredIsFalse receipt
    ; residualGapLocation = phenomenalContentGap
    ; residualGapLocationIsPhenomenal = refl
    ; residualGapStatus = residualStatus phenomenalContentGap
    ; residualGapStatusIsBlocked = refl
    ; missingPromotion = exactMissingPhenomenalPromotion
    ; missingPromotionIsExact = refl
    ; boundaryReading =
        "Physical spin geometry, retinal activation, the visual overlay quotient, and orientation behavior receipt are promoted as constrained observables; phenomenal overlay content remains the exact hard problem residual gap."
    }
