module DASHI.Biology.RetinalPerturbationObservationBridge where

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.AvianCompassSurface
open import DASHI.Biology.AvianCompassExamples

------------------------------------------------------------------------
-- Retinal / perceptual observation vocabulary
------------------------------------------------------------------------

data RetinalPerturbationMode : Set where
  yieldBias : RetinalPerturbationMode
  contrastBias : RetinalPerturbationMode
  salienceGradient : RetinalPerturbationMode
  reliabilityShift : RetinalPerturbationMode

data FormConstantGeometry : Set where
  directionalAxis : FormConstantGeometry
  brightnessGradient : FormConstantGeometry
  latticeField : FormConstantGeometry
  spiralField : FormConstantGeometry
  tunnelField : FormConstantGeometry
  cobwebField : FormConstantGeometry
  diffuseConfidenceField : FormConstantGeometry

data QuotientLoss : Set where
  retinalManyToOne : QuotientLoss
  perceptualManyToOne : QuotientLoss
  reportManyToOne : QuotientLoss
  behavioralManyToOne : QuotientLoss

data ObservationBridgeBoundary : Set where
  boundaryObservationChannelOnly : ObservationBridgeBoundary
  boundaryConstrainedGeometryOnly : ObservationBridgeBoundary
  boundaryNoSubjectiveQualiaClaim : ObservationBridgeBoundary
  boundaryNoBrainClosureClaim : ObservationBridgeBoundary
  boundaryNoCanonicalLatentStateRecovery : ObservationBridgeBoundary
  boundaryNoFMRIValidationClaim : ObservationBridgeBoundary

------------------------------------------------------------------------
-- Retinal perturbation surface
------------------------------------------------------------------------

record RetinalPerturbationSurface
    (surface : AvianCompassSurface) : Set₁ where
  field
    RetinalCoordinate : Set
    RetinalPerturbation : Set
    BaseVisualInput : Set
    PerturbedVisualInput : Set
    YieldClass : Set

    yieldClass :
      RetinalSignal surface →
      YieldClass

    perturbationAt :
      RetinalSignal surface →
      RetinalCoordinate →
      RetinalPerturbation

    perturbationMode :
      RetinalPerturbation →
      RetinalPerturbationMode

    overlay :
      BaseVisualInput →
      RetinalPerturbation →
      PerturbedVisualInput

    perturbationReading : String

open RetinalPerturbationSurface public

------------------------------------------------------------------------
-- Lossy perceptual quotient
------------------------------------------------------------------------

record PerceptualObservationQuotient
    (surface : AvianCompassSurface)
    (retina : RetinalPerturbationSurface surface) : Set₁ where
  field
    PerceptualCarrier : Set
    PerceptualEquivalenceClass : Set
    BehaviourClass : Set
    ReportSurface : Set

    quotient :
      PerturbedVisualInput retina →
      PerceptualCarrier

    geometryClass :
      PerceptualCarrier →
      PerceptualEquivalenceClass

    geometryVocabulary :
      PerceptualEquivalenceClass →
      List FormConstantGeometry

    behaviorClass :
      PerceptualCarrier →
      BehaviourClass

    report :
      PerceptualCarrier →
      ReportSurface

    quotientLosses : List QuotientLoss

    sameObservationMayHaveMultipleLatents :
      PerceptualCarrier →
      Set

    noInjectivityClaim : Bool
    noInjectivityClaimIsTrue :
      noInjectivityClaim ≡ true

    quotientReading : String

open PerceptualObservationQuotient public

------------------------------------------------------------------------
-- Safe avian compass -> retinal perturbation -> quotient bridge
------------------------------------------------------------------------

record RetinalPerturbationObservationBridge
    (surface : AvianCompassSurface) : Set₁ where
  field
    retinalPerturbation :
      RetinalPerturbationSurface surface

    perceptualQuotient :
      PerceptualObservationQuotient surface retinalPerturbation

    compassToPerceptualQuotient :
      (B : MagneticField surface) →
      (θ : FieldAngle surface B) →
      (r : RadicalPair surface) →
      SpinState surface r →
      RetinalCoordinate retinalPerturbation →
      PerceptualCarrier perceptualQuotient

    constrainedGeometryFamily :
      PerceptualCarrier perceptualQuotient →
      List FormConstantGeometry

    behaviorOrientationCue :
      PerceptualCarrier perceptualQuotient →
      NavigationPolicy surface →
      OrientationCue surface

    bridgeBoundaries : List ObservationBridgeBoundary

    nonPromoting : Bool
    nonPromotingIsTrue :
      nonPromoting ≡ true

    noQualiaClaim : Bool
    noQualiaClaimIsTrue :
      noQualiaClaim ≡ true

    noBrainClosureClaim : Bool
    noBrainClosureClaimIsTrue :
      noBrainClosureClaim ≡ true

    safeReading : String

open RetinalPerturbationObservationBridge public

record ObservationBridgeNonPromotionCertificate
    {surface : AvianCompassSurface}
    (bridge : RetinalPerturbationObservationBridge surface) : Set where
  field
    nonPromotionHeld :
      nonPromoting bridge ≡ true

    qualiaClaimBlocked :
      noQualiaClaim bridge ≡ true

    brainClosureBlocked :
      noBrainClosureClaim bridge ≡ true

    boundaryNote : String

open ObservationBridgeNonPromotionCertificate public

------------------------------------------------------------------------
-- Canonical proof-light witness over the avian compass toy carrier.
------------------------------------------------------------------------

canonicalRetinalPerturbationSurface :
  RetinalPerturbationSurface canonicalAvianCompassSurface
canonicalRetinalPerturbationSurface =
  record
    { RetinalCoordinate = BioToken
    ; RetinalPerturbation = BioToken
    ; BaseVisualInput = BioToken
    ; PerturbedVisualInput = BioToken
    ; YieldClass = BioToken
    ; yieldClass = λ _ → retinalYieldSignal
    ; perturbationAt = λ _ _ → visualOverlayToken
    ; perturbationMode = λ _ → salienceGradient
    ; overlay = λ _ _ → visualOverlayToken
    ; perturbationReading =
        "Radical-pair yield is exposed only as a retinal perturbation field."
    }

canonicalPerceptualObservationQuotient :
  PerceptualObservationQuotient
    canonicalAvianCompassSurface
    canonicalRetinalPerturbationSurface
canonicalPerceptualObservationQuotient =
  record
    { PerceptualCarrier = BioToken
    ; PerceptualEquivalenceClass = BioToken
    ; BehaviourClass = BioToken
    ; ReportSurface = BioToken
    ; quotient = λ _ → visualOverlayToken
    ; geometryClass = λ _ → witnessToken
    ; geometryVocabulary =
        λ _ →
          directionalAxis
          ∷ brightnessGradient
          ∷ diffuseConfidenceField
          ∷ []
    ; behaviorClass = λ _ → orientationCueToken
    ; report = λ _ → witnessToken
    ; quotientLosses =
        retinalManyToOne
        ∷ perceptualManyToOne
        ∷ reportManyToOne
        ∷ behavioralManyToOne
        ∷ []
    ; sameObservationMayHaveMultipleLatents = λ _ → BioToken
    ; noInjectivityClaim = true
    ; noInjectivityClaimIsTrue = refl
    ; quotientReading =
        "The perceptual quotient constrains geometry class but is not injective."
    }

canonicalRetinalPerturbationObservationBridge :
  RetinalPerturbationObservationBridge canonicalAvianCompassSurface
canonicalRetinalPerturbationObservationBridge =
  record
    { retinalPerturbation = canonicalRetinalPerturbationSurface
    ; perceptualQuotient = canonicalPerceptualObservationQuotient
    ; compassToPerceptualQuotient =
        λ _ _ _ _ _ → visualOverlayToken
    ; constrainedGeometryFamily =
        λ _ →
          directionalAxis
          ∷ brightnessGradient
          ∷ diffuseConfidenceField
          ∷ []
    ; behaviorOrientationCue =
        λ _ _ → orientationCueToken
    ; bridgeBoundaries =
        boundaryObservationChannelOnly
        ∷ boundaryConstrainedGeometryOnly
        ∷ boundaryNoSubjectiveQualiaClaim
        ∷ boundaryNoBrainClosureClaim
        ∷ boundaryNoCanonicalLatentStateRecovery
        ∷ boundaryNoFMRIValidationClaim
        ∷ []
    ; nonPromoting = true
    ; nonPromotingIsTrue = refl
    ; noQualiaClaim = true
    ; noQualiaClaimIsTrue = refl
    ; noBrainClosureClaim = true
    ; noBrainClosureClaimIsTrue = refl
    ; safeReading =
        "Avian compass transport reaches a constrained geometry class, not qualia or brain closure."
    }

canonicalObservationBridgeNonPromotionCertificate :
  ObservationBridgeNonPromotionCertificate
    canonicalRetinalPerturbationObservationBridge
canonicalObservationBridgeNonPromotionCertificate =
  record
    { nonPromotionHeld = refl
    ; qualiaClaimBlocked = refl
    ; brainClosureBlocked = refl
    ; boundaryNote =
        "The bridge is observation-only and blocks qualia and brain-closure promotion."
    }
