module DASHI.Foundations.HexTruthPolarityFactor where

open import Agda.Builtin.Equality using (_≡_; refl)

open import DASHI.Core.Prelude using
  (_×_; _,_; proj₁; proj₂)

open import Base369 using
  ( HexTruth
  ; TriTruth
  ; tri-low
  ; tri-mid
  ; tri-high
  ; hex-0
  ; hex-1
  ; hex-2
  ; hex-3
  ; hex-4
  ; hex-5
  )

open import DASHI.Foundations.Base369MobiusTransport using
  ( OrientationPolarity
  ; positive
  ; negative
  ; flipOrientationPolarity
  ; hexTriadicPhase
  ; hexOrientationPolarity
  ; mobiusTransport
  )

------------------------------------------------------------------------
-- Polarity bit.
------------------------------------------------------------------------

Polarity : Set
Polarity = OrientationPolarity

flipPolarity : Polarity → Polarity
flipPolarity = flipOrientationPolarity

------------------------------------------------------------------------
-- Typed factorization HexTruth ≅ TriTruth × Polarity.
------------------------------------------------------------------------

hexTruthToFactor : HexTruth → TriTruth × Polarity
hexTruthToFactor hex-0 = tri-low , positive
hexTruthToFactor hex-1 = tri-mid , positive
hexTruthToFactor hex-2 = tri-high , positive
hexTruthToFactor hex-3 = tri-low , negative
hexTruthToFactor hex-4 = tri-mid , negative
hexTruthToFactor hex-5 = tri-high , negative

hexFactorToTruth : TriTruth → Polarity → HexTruth
hexFactorToTruth tri-low  positive = hex-0
hexFactorToTruth tri-low  negative = hex-3
hexFactorToTruth tri-mid  positive = hex-1
hexFactorToTruth tri-mid  negative = hex-4
hexFactorToTruth tri-high positive = hex-2
hexFactorToTruth tri-high negative = hex-5

------------------------------------------------------------------------
-- Projection laws: decode is faithful to canonical triadic phase and polarity.
------------------------------------------------------------------------

hexTruthToFactor-projectTri : ∀ x → proj₁ (hexTruthToFactor x) ≡ hexTriadicPhase x
hexTruthToFactor-projectTri hex-0 = refl
hexTruthToFactor-projectTri hex-1 = refl
hexTruthToFactor-projectTri hex-2 = refl
hexTruthToFactor-projectTri hex-3 = refl
hexTruthToFactor-projectTri hex-4 = refl
hexTruthToFactor-projectTri hex-5 = refl

hexTruthToFactor-projectPolarity :
  ∀ x → proj₂ (hexTruthToFactor x) ≡ hexOrientationPolarity x
hexTruthToFactor-projectPolarity hex-0 = refl
hexTruthToFactor-projectPolarity hex-1 = refl
hexTruthToFactor-projectPolarity hex-2 = refl
hexTruthToFactor-projectPolarity hex-3 = refl
hexTruthToFactor-projectPolarity hex-4 = refl
hexTruthToFactor-projectPolarity hex-5 = refl

------------------------------------------------------------------------
-- Roundtrip laws.
------------------------------------------------------------------------

hexTruthToFactor-decodingRoundTrip :
  ∀ x → hexFactorToTruth (proj₁ (hexTruthToFactor x)) (proj₂ (hexTruthToFactor x)) ≡ x
hexTruthToFactor-decodingRoundTrip hex-0 = refl
hexTruthToFactor-decodingRoundTrip hex-1 = refl
hexTruthToFactor-decodingRoundTrip hex-2 = refl
hexTruthToFactor-decodingRoundTrip hex-3 = refl
hexTruthToFactor-decodingRoundTrip hex-4 = refl
hexTruthToFactor-decodingRoundTrip hex-5 = refl

hexFactorToTruth-encodingRoundTrip :
  ∀ t p → hexTruthToFactor (hexFactorToTruth t p) ≡ (t , p)
hexFactorToTruth-encodingRoundTrip tri-low  positive = refl
hexFactorToTruth-encodingRoundTrip tri-low  negative = refl
hexFactorToTruth-encodingRoundTrip tri-mid  positive = refl
hexFactorToTruth-encodingRoundTrip tri-mid  negative = refl
hexFactorToTruth-encodingRoundTrip tri-high positive = refl
hexFactorToTruth-encodingRoundTrip tri-high negative = refl

------------------------------------------------------------------------
-- Möbius transport as pair action id × flip on the factorization.
------------------------------------------------------------------------

mobiusTransport-factors :
  ∀ x →
  hexTruthToFactor (mobiusTransport x) ≡
  (proj₁ (hexTruthToFactor x) , flipPolarity (proj₂ (hexTruthToFactor x)))
mobiusTransport-factors hex-0 = refl
mobiusTransport-factors hex-1 = refl
mobiusTransport-factors hex-2 = refl
mobiusTransport-factors hex-3 = refl
mobiusTransport-factors hex-4 = refl
mobiusTransport-factors hex-5 = refl

