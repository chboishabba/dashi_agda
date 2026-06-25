module DASHI.Physics.YangMills.BalabanPolymerDiameterEntropy where

open import Agda.Builtin.Bool using (Bool; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat)
open import Agda.Builtin.String using (String)
open import Data.List.Base using (List; _∷_; [])

open import DASHI.Geometry.Gauge.SUNPrimitives using (clayYangMillsPromoted)

Scalar : Set
Scalar = String

data StubPolymer : Set where
  stubPolymer : StubPolymer

data PolymerDiameterEntropyObligation : Set where
  rootedTouchingPolymerCounting : PolymerDiameterEntropyObligation
  connectedShapeEntropyRate : PolymerDiameterEntropyObligation
  volumeUniformRootBound : PolymerDiameterEntropyObligation

canonicalPolymerDiameterEntropyObligations :
  List PolymerDiameterEntropyObligation
canonicalPolymerDiameterEntropyObligations =
  rootedTouchingPolymerCounting
  ∷ connectedShapeEntropyRate
  ∷ volumeUniformRootBound
  ∷ []

record PolymerGeometry : Set₁ where
  field
    Polymer : Set
    diameter : Polymer → Nat
    weight : Polymer → Scalar
    touches : Polymer → Polymer → Bool
    containsRoot : Polymer → Bool

canonicalPolymerGeometry : PolymerGeometry
canonicalPolymerGeometry = record
  { Polymer = StubPolymer
  ; diameter = λ _ → 0
  ; weight = λ _ → "candidate"
  ; touches = λ _ _ → false
  ; containsRoot = λ _ → false
  }

record PolymerDiameterEntropyBound : Set₁ where
  field
    geom : PolymerGeometry
    entropyRate : Scalar
    entropyControlled : Bool
    polymerCountBound : Bool
    rootedTouchingCountBound : Bool
    volumeIndependentEntropyRate : Bool
    entropyControlledIsFalse : entropyControlled ≡ false
    polymerCountBoundIsFalse : polymerCountBound ≡ false
    rootedTouchingCountBoundIsFalse : rootedTouchingCountBound ≡ false
    volumeIndependentEntropyRateIsFalse :
      volumeIndependentEntropyRate ≡ false
    targetInequality : String
    openObligations : List PolymerDiameterEntropyObligation
    openObligationsAreCanonical :
      openObligations ≡ canonicalPolymerDiameterEntropyObligations
    noClayPromotion : clayYangMillsPromoted ≡ false

currentPolymerDiameterEntropyBound : PolymerDiameterEntropyBound
currentPolymerDiameterEntropyBound = record
  { geom = canonicalPolymerGeometry
  ; entropyRate = "unproved"
  ; entropyControlled = false
  ; polymerCountBound = false
  ; rootedTouchingCountBound = false
  ; volumeIndependentEntropyRate = false
  ; entropyControlledIsFalse = refl
  ; polymerCountBoundIsFalse = refl
  ; rootedTouchingCountBoundIsFalse = refl
  ; volumeIndependentEntropyRateIsFalse = refl
  ; targetInequality =
      "count(polymers of diameter d touching root) <= C * exp(kappa * d)"
  ; openObligations = canonicalPolymerDiameterEntropyObligations
  ; openObligationsAreCanonical = refl
  ; noClayPromotion = refl
  }
