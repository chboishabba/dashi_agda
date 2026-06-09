module DASHI.Biology.AvianCompassSurface where

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Agda.Builtin.String using (String)

------------------------------------------------------------------------
-- Layer and carrier vocabulary
------------------------------------------------------------------------

data SpinBasis : Set where
  singlet : SpinBasis
  triplet0 : SpinBasis
  tripletPlus : SpinBasis
  tripletMinus : SpinBasis

data BridgeLayer : Set where
  photonLayer : BridgeLayer
  cry4ActivationLayer : BridgeLayer
  radicalPairLayer : BridgeLayer
  spinEvolutionLayer : BridgeLayer
  singletTripletYieldLayer : BridgeLayer
  retinalChemicalLayer : BridgeLayer
  visualCueLayer : BridgeLayer
  navigationPolicyLayer : BridgeLayer

data PerceptualGeometry : Set where
  directionalBrightnessModulation : PerceptualGeometry
  interferenceTextureOverlay : PerceptualGeometry
  polarizationLikeAnisotropy : PerceptualGeometry
  confidenceWeightingField : PerceptualGeometry

data PerturbationRegime : Set where
  noPerturbation : PerturbationRegime
  staticLocalMagnet : PerturbationRegime
  oscillatingRFField : PerturbationRegime

data OrientationEffect : Set where
  stableHeading : OrientationEffect
  shiftedHeading : OrientationEffect
  randomHeading : OrientationEffect
  refusalToOrient : OrientationEffect
  invertedCompass : OrientationEffect
  degradedConfidence : OrientationEffect

data ClaimBoundary : Set where
  observableBehaviourOnly : ClaimBoundary
  noSubjectiveQualiaRecovery : ClaimBoundary
  noDirectMagneticVisionClaim : ClaimBoundary
  noCompleteBiophysicalMechanismClaim : ClaimBoundary
  noEthicalPerturbationLicense : ClaimBoundary

------------------------------------------------------------------------
-- Surface object
------------------------------------------------------------------------

record AvianCompassSurface : Set₁ where
  field
    PhotonInput : Set
    Cryptochrome4 : Set
    RadicalPair : Set
    MagneticField : Set
    Hamiltonian : Set
    RetinalSignal : Set
    VisualPattern : Set
    OrientationCue : Set
    NavigationPolicy : Set

    SpinState : RadicalPair → Set
    FieldAngle : MagneticField → Set

    singletComponent : (r : RadicalPair) → SpinState r → SpinBasis
    tripletComponents : (r : RadicalPair) → SpinState r → List SpinBasis

    lightGated : PhotonInput → Cryptochrome4 → RadicalPair

    hyperfineHamiltonian : RadicalPair → Hamiltonian
    zeemanHamiltonian : (B : MagneticField) → FieldAngle B → Hamiltonian
    fieldHamiltonian : (B : MagneticField) → FieldAngle B → Hamiltonian

    evolve :
      (B : MagneticField) →
      (θ : FieldAngle B) →
      (r : RadicalPair) →
      SpinState r →
      SpinState r

    yield :
      (B : MagneticField) →
      (θ : FieldAngle B) →
      (r : RadicalPair) →
      SpinState r →
      RetinalSignal

    angleDistinguishable :
      (B₁ B₂ : MagneticField) →
      FieldAngle B₁ →
      FieldAngle B₂ →
      Set

    yieldDistinguishable :
      RetinalSignal →
      RetinalSignal →
      Set

    angleSensitive :
      (B₁ B₂ : MagneticField) →
      (θ₁ : FieldAngle B₁) →
      (θ₂ : FieldAngle B₂) →
      (r : RadicalPair) →
      (ψ : SpinState r) →
      angleDistinguishable B₁ B₂ θ₁ θ₂ →
      yieldDistinguishable
        (yield B₁ θ₁ r ψ)
        (yield B₂ θ₂ r ψ)

    visualCue : RetinalSignal → VisualPattern
    navigationUse : VisualPattern → NavigationPolicy → OrientationCue

open AvianCompassSurface public

record AvianCompassBridgeReceipt : Set₁ where
  field
    surface : AvianCompassSurface
    bridgeChain : List BridgeLayer
    perceptualGeometries : List PerceptualGeometry
    perturbationRegimes : List PerturbationRegime
    promotedBiologicalObservable : Bool
    promotedBiologicalObservableIsTrue :
      promotedBiologicalObservable ≡ true
    subjectiveQualiaRecovered : Bool
    subjectiveQualiaRecoveredIsFalse :
      subjectiveQualiaRecovered ≡ false
    nonPromotionBoundary : List ClaimBoundary
    plainReading : String

open AvianCompassBridgeReceipt public

record PerturbedCompassReceipt
    (surface : AvianCompassSurface) : Set₁ where
  field
    perturbation : PerturbationRegime
    baseField : MagneticField surface
    perturbedField : MagneticField surface
    baseAngle : FieldAngle surface baseField
    perturbedAngle : FieldAngle surface perturbedField
    radicalPair : RadicalPair surface
    spinState : SpinState surface radicalPair
    angleChanged :
      angleDistinguishable surface
        baseField
        perturbedField
        baseAngle
        perturbedAngle
    yieldChanged :
      yieldDistinguishable surface
        (yield surface baseField baseAngle radicalPair spinState)
        (yield surface perturbedField perturbedAngle radicalPair spinState)
    orientationEffect : OrientationEffect
    noPanicClaim : Bool
    noPanicClaimIsTrue : noPanicClaim ≡ true

open PerturbedCompassReceipt public

record ObservableNotQualiaBoundary
    (receipt : AvianCompassBridgeReceipt) : Set where
  field
    observableSurfaceConstrained :
      promotedBiologicalObservable receipt ≡ true
    qualiaSurfaceUnrecovered :
      subjectiveQualiaRecovered receipt ≡ false
    boundaryNote : String

open ObservableNotQualiaBoundary public
