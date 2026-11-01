module DASHI.Biology.AvianCompassExamples where

open import Agda.Builtin.Bool using (true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)

open import DASHI.Biology.AvianCompassSurface

------------------------------------------------------------------------
-- Toy carrier
------------------------------------------------------------------------

data BioToken : Set where
  bluePhoton : BioToken
  cry4Carrier : BioToken
  radicalPairToken : BioToken
  spinStateToken : BioToken
  earthField : BioToken
  localMagnetField : BioToken
  rfPerturbedField : BioToken
  earthInclination : BioToken
  localMagnetInclination : BioToken
  rfNoisyInclination : BioToken
  hyperfineTerm : BioToken
  zeemanTerm : BioToken
  combinedHamiltonian : BioToken
  retinalYieldSignal : BioToken
  visualOverlayToken : BioToken
  migrationPolicyToken : BioToken
  orientationCueToken : BioToken
  witnessToken : BioToken

tokenList : List BioToken
tokenList = witnessToken ∷ []

canonicalAvianCompassSurface : AvianCompassSurface
canonicalAvianCompassSurface =
  record
    { PhotonInput = BioToken
    ; Cryptochrome4 = BioToken
    ; RadicalPair = BioToken
    ; MagneticField = BioToken
    ; Hamiltonian = BioToken
    ; RetinalSignal = BioToken
    ; VisualPattern = BioToken
    ; OrientationCue = BioToken
    ; NavigationPolicy = BioToken
    ; SpinState = λ _ → BioToken
    ; FieldAngle = λ _ → BioToken
    ; singletComponent = λ _ _ → singlet
    ; tripletComponents = λ _ _ → triplet0 ∷ tripletPlus ∷ tripletMinus ∷ []
    ; lightGated = λ _ _ → radicalPairToken
    ; hyperfineHamiltonian = λ _ → hyperfineTerm
    ; zeemanHamiltonian = λ _ _ → zeemanTerm
    ; fieldHamiltonian = λ _ _ → combinedHamiltonian
    ; evolve = λ _ _ _ ψ → ψ
    ; yield = λ _ _ _ _ → retinalYieldSignal
    ; angleDistinguishable = λ _ _ _ _ → BioToken
    ; yieldDistinguishable = λ _ _ → BioToken
    ; angleSensitive = λ _ _ _ _ _ _ _ → witnessToken
    ; visualCue = λ _ → visualOverlayToken
    ; navigationUse = λ _ _ → orientationCueToken
    }

canonicalBridgeChain : List BridgeLayer
canonicalBridgeChain =
  photonLayer
  ∷ cry4ActivationLayer
  ∷ radicalPairLayer
  ∷ spinEvolutionLayer
  ∷ singletTripletYieldLayer
  ∷ retinalChemicalLayer
  ∷ visualCueLayer
  ∷ navigationPolicyLayer
  ∷ []

canonicalPerceptualGeometries : List PerceptualGeometry
canonicalPerceptualGeometries =
  directionalBrightnessModulation
  ∷ interferenceTextureOverlay
  ∷ polarizationLikeAnisotropy
  ∷ confidenceWeightingField
  ∷ []

canonicalPerturbationRegimes : List PerturbationRegime
canonicalPerturbationRegimes =
  noPerturbation ∷ staticLocalMagnet ∷ oscillatingRFField ∷ []

canonicalAvianCompassBridgeReceipt : AvianCompassBridgeReceipt
canonicalAvianCompassBridgeReceipt =
  record
    { surface = canonicalAvianCompassSurface
    ; bridgeChain = canonicalBridgeChain
    ; perceptualGeometries = canonicalPerceptualGeometries
    ; perturbationRegimes = canonicalPerturbationRegimes
    ; promotedBiologicalObservable = true
    ; promotedBiologicalObservableIsTrue = refl
    ; subjectiveQualiaRecovered = false
    ; subjectiveQualiaRecoveredIsFalse = refl
    ; nonPromotionBoundary =
        observableBehaviourOnly
        ∷ noSubjectiveQualiaRecovery
        ∷ noDirectMagneticVisionClaim
        ∷ noCompleteBiophysicalMechanismClaim
        ∷ noEthicalPerturbationLicense
        ∷ []
    ; plainReading =
        "Quantum spin residual is promoted only through retinal chemistry into an orientation observable."
    }

lightGatedRadicalPairWitness :
  lightGated canonicalAvianCompassSurface bluePhoton cry4Carrier ≡ radicalPairToken
lightGatedRadicalPairWitness = refl

spinEvolutionWitness :
  evolve
    canonicalAvianCompassSurface
    earthField
    earthInclination
    radicalPairToken
    spinStateToken
  ≡
  spinStateToken
spinEvolutionWitness = refl

yieldToRetinaWitness :
  yield
    canonicalAvianCompassSurface
    earthField
    earthInclination
    radicalPairToken
    spinStateToken
  ≡
  retinalYieldSignal
yieldToRetinaWitness = refl

visualNavigationWitness :
  navigationUse
    canonicalAvianCompassSurface
    (visualCue canonicalAvianCompassSurface retinalYieldSignal)
    migrationPolicyToken
  ≡
  orientationCueToken
visualNavigationWitness = refl

staticMagnetPerturbationReceipt :
  PerturbedCompassReceipt canonicalAvianCompassSurface
staticMagnetPerturbationReceipt =
  record
    { perturbation = staticLocalMagnet
    ; baseField = earthField
    ; perturbedField = localMagnetField
    ; baseAngle = earthInclination
    ; perturbedAngle = localMagnetInclination
    ; radicalPair = radicalPairToken
    ; spinState = spinStateToken
    ; angleChanged = witnessToken
    ; yieldChanged = witnessToken
    ; orientationEffect = shiftedHeading
    ; noPanicClaim = true
    ; noPanicClaimIsTrue = refl
    }

rfPerturbationReceipt :
  PerturbedCompassReceipt canonicalAvianCompassSurface
rfPerturbationReceipt =
  record
    { perturbation = oscillatingRFField
    ; baseField = earthField
    ; perturbedField = rfPerturbedField
    ; baseAngle = earthInclination
    ; perturbedAngle = rfNoisyInclination
    ; radicalPair = radicalPairToken
    ; spinState = spinStateToken
    ; angleChanged = witnessToken
    ; yieldChanged = witnessToken
    ; orientationEffect = degradedConfidence
    ; noPanicClaim = true
    ; noPanicClaimIsTrue = refl
    }

rfRandomHeadingEffect : OrientationEffect
rfRandomHeadingEffect = randomHeading

rfRefusalEffect : OrientationEffect
rfRefusalEffect = refusalToOrient

staticInversionEffect : OrientationEffect
staticInversionEffect = invertedCompass

observableNotQualiaBoundary :
  ObservableNotQualiaBoundary canonicalAvianCompassBridgeReceipt
observableNotQualiaBoundary =
  record
    { observableSurfaceConstrained = refl
    ; qualiaSurfaceUnrecovered = refl
    ; boundaryNote =
        "Observable orientation transport does not recover subjective magnetic qualia."
    }
