module Ontology.DNA.FixedPointTernaryAndTetration where

open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.Nat using (Nat; zero; suc; _+_; _*_)
open import Data.Fin.Base using (Fin)

open import Ontology.DNA.ChemistryTernaryQuantizer using
  (Trit; minus; neutral; plus)

------------------------------------------------------------------------
-- Exact bounded fixed-point ternary distortion.
-- This is the current proved quantitative statement.  It is not silently
-- identified with an analytic theorem over the completed real numbers.

data ResidualUnit : Set where
  below centre above : ResidualUnit

record FixedPointCoefficient : Set where
  constructor coefficient
  field
    basin : Trit
    residual : ResidualUnit

quantize : FixedPointCoefficient → Trit
quantize c = FixedPointCoefficient.basin c

reconstruct : Trit → FixedPointCoefficient
reconstruct t = coefficient t centre

distortion : FixedPointCoefficient → Nat
distortion (coefficient t below) = suc zero
distortion (coefficient t centre) = zero
distortion (coefficient t above) = suc zero

data _≤_ : Nat → Nat → Set where
  z≤n : ∀ {n} → zero ≤ n
  s≤s : ∀ {m n} → m ≤ n → suc m ≤ suc n

distortion-at-most-one : ∀ c → distortion c ≤ suc zero
distortion-at-most-one (coefficient t below) = s≤s z≤n
distortion-at-most-one (coefficient t centre) = z≤n
distortion-at-most-one (coefficient t above) = s≤s z≤n

quantize-reconstructed : ∀ t → quantize (reconstruct t) ≡ t
quantize-reconstructed minus = refl
quantize-reconstructed neutral = refl
quantize-reconstructed plus = refl

record AnalyticRealPromotion : Set₁ where
  field
    Real : Set
    absDistance : Real → Real → Real
    threshold : Real
    quantizer : Real → Trit
    representative : Trit → Real
    orderedBound : Set

------------------------------------------------------------------------
-- Exact finite tetration recurrence for transform-context cardinalities.

pow : Nat → Nat → Nat
pow base zero = suc zero
pow base (suc n) = base * pow base n

tetrate : Nat → Nat → Nat
tetrate base zero = suc zero
tetrate base (suc height) = pow base (tetrate base height)

tetrate-step : ∀ base height →
  tetrate base (suc height) ≡ pow base (tetrate base height)
tetrate-step base height = refl

TransformContextCode : Nat → Nat → Set
TransformContextCode base height = Fin (tetrate base height)

context-cardinality-step : ∀ base height →
  TransformContextCode base (suc height) ≡ Fin (pow base (tetrate base height))
context-cardinality-step base height = refl

four-height-two : tetrate 4 (suc (suc zero)) ≡ 256
four-height-two = refl

record PhysicalEmbeddingBoundary : Set₁ where
  field
    physicalCarrier : Set
    contextHeight : Nat
    embedding : physicalCarrier → TransformContextCode 4 contextHeight
    injective : Set
    semanticsPreserved : Set
