module DASHI.Biology.AvianVisualOverlayQuotient where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

open import DASHI.Biology.AvianCompassSurface

------------------------------------------------------------------------
-- Visual-field and quotient vocabulary
------------------------------------------------------------------------

data VisualFieldRegion : Set where
  dorsalRetina : VisualFieldRegion
  ventralRetina : VisualFieldRegion
  temporalField : VisualFieldRegion
  nasalField : VisualFieldRegion
  binocularBand : VisualFieldRegion
  horizonBand : VisualFieldRegion
  wholeVisualField : VisualFieldRegion

data OverlayGeometryClass : Set where
  brightnessGradientOverlay : OverlayGeometryClass
  contrastTextureOverlay : OverlayGeometryClass
  inclinationAxisOverlay : OverlayGeometryClass
  headingConfidenceOverlay : OverlayGeometryClass
  fieldPerturbationShadow : OverlayGeometryClass

data BehavioralEquivalence : Set where
  sameOrientationCue : BehavioralEquivalence
  sameHeadingChoice : BehavioralEquivalence
  samePerturbationResponse : BehavioralEquivalence
  sameNavigationPolicyUse : BehavioralEquivalence

data PerceptualEquivalence : Set where
  sameRetinalSignalClass : PerceptualEquivalence
  sameVisualPatternClass : PerceptualEquivalence
  sameOverlayGeometryClass : PerceptualEquivalence
  noPhenomenalIdentityClaim : PerceptualEquivalence

data NonPromotionBoundary : Set where
  quotientOnlyBoundary : NonPromotionBoundary
  noPhenomenalIdentityBoundary : NonPromotionBoundary
  noQualiaRecoveryBoundary : NonPromotionBoundary
  noDirectSubjectiveReportBoundary : NonPromotionBoundary
  noFirstPersonContentBoundary : NonPromotionBoundary
  noEthologyToExperiencePromotionBoundary : NonPromotionBoundary

------------------------------------------------------------------------
-- Overlay quotient constraint
------------------------------------------------------------------------

record AvianVisualOverlayQuotient
    (surface : AvianCompassSurface) : Set₁ where
  field
    photon : PhotonInput surface
    cryptochrome4 : Cryptochrome4 surface
    magneticField : MagneticField surface
    fieldAngle : FieldAngle surface magneticField
    navigationPolicy : NavigationPolicy surface

    radicalPair : RadicalPair surface
    initialSpinState : SpinState surface radicalPair
    evolvedSpinState : SpinState surface radicalPair
    retinalSignal : RetinalSignal surface
    visualPattern : VisualPattern surface
    orientationCue : OrientationCue surface

    radicalPairFromLightGate :
      radicalPair ≡ lightGated surface photon cryptochrome4
    evolvedFromSpinDynamics :
      evolvedSpinState ≡
      evolve surface magneticField fieldAngle radicalPair initialSpinState
    retinalSignalFromYield :
      retinalSignal ≡
      yield surface magneticField fieldAngle radicalPair evolvedSpinState
    visualPatternFromRetina :
      visualPattern ≡ visualCue surface retinalSignal
    orientationCueFromOverlay :
      orientationCue ≡ navigationUse surface visualPattern navigationPolicy

    fieldRegions : List VisualFieldRegion
    overlayGeometries : List OverlayGeometryClass
    behavioralEquivalences : List BehavioralEquivalence
    perceptualEquivalences : List PerceptualEquivalence
    nonPromotionBoundaries : List NonPromotionBoundary

    quotientConstraintPromoted : Bool
    quotientConstraintPromotedIsTrue :
      quotientConstraintPromoted ≡ true

    phenomenalIdentityBlocked : Bool
    phenomenalIdentityBlockedIsTrue :
      phenomenalIdentityBlocked ≡ true

    qualiaRecoveryBlocked : Bool
    qualiaRecoveryBlockedIsTrue :
      qualiaRecoveryBlocked ≡ true

    directSubjectiveReportBlocked : Bool
    directSubjectiveReportBlockedIsTrue :
      directSubjectiveReportBlocked ≡ true

    subjectiveQualiaRecovered : Bool
    subjectiveQualiaRecoveredIsFalse :
      subjectiveQualiaRecovered ≡ false

    quotientBoundary : String
    phenomenalIdentityBoundary : String
    qualiaBoundary : String
    reportBoundary : String
    plainReading : String

open AvianVisualOverlayQuotient public

canonicalRegions : List VisualFieldRegion
canonicalRegions =
  dorsalRetina ∷ horizonBand ∷ binocularBand ∷ wholeVisualField ∷ []

canonicalOverlayGeometries : List OverlayGeometryClass
canonicalOverlayGeometries =
  brightnessGradientOverlay
  ∷ contrastTextureOverlay
  ∷ inclinationAxisOverlay
  ∷ headingConfidenceOverlay
  ∷ []

canonicalBehavioralEquivalences : List BehavioralEquivalence
canonicalBehavioralEquivalences =
  sameOrientationCue ∷ sameHeadingChoice ∷ sameNavigationPolicyUse ∷ []

canonicalPerceptualEquivalences : List PerceptualEquivalence
canonicalPerceptualEquivalences =
  sameRetinalSignalClass
  ∷ sameVisualPatternClass
  ∷ sameOverlayGeometryClass
  ∷ noPhenomenalIdentityClaim
  ∷ []

canonicalNonPromotionBoundaries : List NonPromotionBoundary
canonicalNonPromotionBoundaries =
  quotientOnlyBoundary
  ∷ noPhenomenalIdentityBoundary
  ∷ noQualiaRecoveryBoundary
  ∷ noDirectSubjectiveReportBoundary
  ∷ noFirstPersonContentBoundary
  ∷ noEthologyToExperiencePromotionBoundary
  ∷ []

canonicalOverlayQuotient :
  (surface : AvianCompassSurface) →
  (photon : PhotonInput surface) →
  (cryptochrome4 : Cryptochrome4 surface) →
  (magneticField : MagneticField surface) →
  (fieldAngle : FieldAngle surface magneticField) →
  (navigationPolicy : NavigationPolicy surface) →
  (initialSpinState :
    SpinState surface (lightGated surface photon cryptochrome4)) →
  AvianVisualOverlayQuotient surface
canonicalOverlayQuotient
  surface
  photon
  cryptochrome4
  magneticField
  fieldAngle
  navigationPolicy
  initialSpinState =
  record
    { photon = photon
    ; cryptochrome4 = cryptochrome4
    ; magneticField = magneticField
    ; fieldAngle = fieldAngle
    ; navigationPolicy = navigationPolicy
    ; radicalPair = lightGated surface photon cryptochrome4
    ; initialSpinState = initialSpinState
    ; evolvedSpinState =
        evolve
          surface
          magneticField
          fieldAngle
          (lightGated surface photon cryptochrome4)
          initialSpinState
    ; retinalSignal =
        yield
          surface
          magneticField
          fieldAngle
          (lightGated surface photon cryptochrome4)
          (evolve
            surface
            magneticField
            fieldAngle
            (lightGated surface photon cryptochrome4)
            initialSpinState)
    ; visualPattern =
        visualCue
          surface
          (yield
            surface
            magneticField
            fieldAngle
            (lightGated surface photon cryptochrome4)
            (evolve
              surface
              magneticField
              fieldAngle
              (lightGated surface photon cryptochrome4)
              initialSpinState))
    ; orientationCue =
        navigationUse
          surface
          (visualCue
            surface
            (yield
              surface
              magneticField
              fieldAngle
              (lightGated surface photon cryptochrome4)
              (evolve
                surface
                magneticField
                fieldAngle
                (lightGated surface photon cryptochrome4)
                initialSpinState)))
          navigationPolicy
    ; radicalPairFromLightGate = refl
    ; evolvedFromSpinDynamics = refl
    ; retinalSignalFromYield = refl
    ; visualPatternFromRetina = refl
    ; orientationCueFromOverlay = refl
    ; fieldRegions = canonicalRegions
    ; overlayGeometries = canonicalOverlayGeometries
    ; behavioralEquivalences = canonicalBehavioralEquivalences
    ; perceptualEquivalences = canonicalPerceptualEquivalences
    ; nonPromotionBoundaries = canonicalNonPromotionBoundaries
    ; quotientConstraintPromoted = true
    ; quotientConstraintPromotedIsTrue = refl
    ; phenomenalIdentityBlocked = true
    ; phenomenalIdentityBlockedIsTrue = refl
    ; qualiaRecoveryBlocked = true
    ; qualiaRecoveryBlockedIsTrue = refl
    ; directSubjectiveReportBlocked = true
    ; directSubjectiveReportBlockedIsTrue = refl
    ; subjectiveQualiaRecovered = false
    ; subjectiveQualiaRecoveredIsFalse = refl
    ; quotientBoundary =
        "Quotient identifies retinal and behavioral overlay constraints, not first-person experience."
    ; phenomenalIdentityBoundary =
        "No visual overlay geometry is promoted to phenomenal identity."
    ; qualiaBoundary =
        "CRY4 spin-yield structure constrains an observable cue while qualia recovery remains blocked."
    ; reportBoundary =
        "The bird supplies navigation behavior, not a direct subjective report."
    ; plainReading =
        "Photon-gated CRY4 radical-pair dynamics are mapped through yield, retina, visual pattern, and navigation use into a magnetic visual overlay quotient constraint."
    }

record OverlayQuotientNonPromotion
    {surface : AvianCompassSurface}
    (quotient : AvianVisualOverlayQuotient surface) : Set where
  field
    promotedConstraint :
      quotientConstraintPromoted quotient ≡ true
    phenomenalIdentityNotPromoted :
      phenomenalIdentityBlocked quotient ≡ true
    qualiaNotRecovered :
      subjectiveQualiaRecovered quotient ≡ false
    directReportNotPromoted :
      directSubjectiveReportBlocked quotient ≡ true
    boundarySummary : String

open OverlayQuotientNonPromotion public

canonicalNonPromotion :
  {surface : AvianCompassSurface} →
  (quotient : AvianVisualOverlayQuotient surface) →
  OverlayQuotientNonPromotion quotient
canonicalNonPromotion quotient =
  record
    { promotedConstraint =
        quotientConstraintPromotedIsTrue quotient
    ; phenomenalIdentityNotPromoted =
        phenomenalIdentityBlockedIsTrue quotient
    ; qualiaNotRecovered =
        subjectiveQualiaRecoveredIsFalse quotient
    ; directReportNotPromoted =
        directSubjectiveReportBlockedIsTrue quotient
    ; boundarySummary =
        "Overlay quotient is a constraint seed over observables; qualia and direct report remain outside the promoted surface."
    }
