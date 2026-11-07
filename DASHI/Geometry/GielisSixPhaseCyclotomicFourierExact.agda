{-# OPTIONS --safe #-}
module DASHI.Geometry.GielisSixPhaseCyclotomicFourierExact where

------------------------------------------------------------------------
-- GIELIS SELECTED C6 = C2 x C3 EXACT FOURIER (NO NEW COMPLEX SCALAR)
--
-- Reuses the ACTUAL native C3 Cyclotomic3 arithmetic and BOTH C3
-- Fourier round-trip theorems in C3CubeCyclotomicFourierExact.
--
-- For j mod 6, CRT j |-> (j mod 2, j mod 3):
--
--   even, mod3=0,1,2 -> original C18 j=0,4,2
--   odd,  mod3=0,1,2 -> original C18 j=3,1,5.
--
-- This is the six-phase subcarrier for the 18-sample Gielis mode 3
-- and contains the 3-cycle sampled mode 6. It is NOT a full 18/36
-- point scalar realisation, nor the C36 cyclotomic 12D proof.
------------------------------------------------------------------------

open import Agda.Builtin.Equality using (_≡_; refl)
open import Data.Rational.Base using (ℚ; ½; 1ℚ; -_)
open import Relation.Binary.PropositionalEquality using (cong; trans)
import Data.Rational.Tactic.RingSolver as Ring

import DASHI.Biology.Physical.C3CubeCyclotomicFourierExact as C3
import DASHI.Foundations.Base369CirclePhase as Phase

record Pair (A : Set) : Set where
  constructor pair
  field
    left right : A

open Pair public

pair-ext : ∀ {A : Set} {a b c d : A} →
  a ≡ c → b ≡ d →
  pair a b ≡ pair c d
pair-ext refl refl = refl

mapPair : ∀ {A B : Set} → (A → B) → Pair A → Pair B
mapPair f (pair a b) = pair (f a) (f b)

C2Signal : Set
C2Signal = Pair C3.Cyclotomic3

negC : C3.Cyclotomic3 → C3.Cyclotomic3
negC = C3.scaleC (- 1ℚ)

forward2 : C2Signal → C2Signal
forward2 (pair a b) =
  pair (C3._+C_ a b)
       (C3._+C_ a (negC b))

inverse2 : C2Signal → C2Signal
inverse2 (pair a b) =
  pair (C3.scaleC ½ (C3._+C_ a b))
       (C3.scaleC ½ (C3._+C_ a (negC b)))

twoRoundTrip : ∀ x → inverse2 (forward2 x) ≡ x
twoRoundTrip (pair (C3.cyc a b) (C3.cyc c d)) =
  pair-ext
    (C3.cyc-ext Ring.solve-∀ Ring.solve-∀)
    (C3.cyc-ext Ring.solve-∀ Ring.solve-∀)

twoForwardInverse : ∀ x → forward2 (inverse2 x) ≡ x
twoForwardInverse (pair (C3.cyc a b) (C3.cyc c d)) =
  pair-ext
    (C3.cyc-ext Ring.solve-∀ Ring.solve-∀)
    (C3.cyc-ext Ring.solve-∀ Ring.solve-∀)

TripleC : Set
TripleC = C3.Triple C3.Cyclotomic3

SixSignal : Set
SixSignal = Pair TripleC

tripleAdd : TripleC → TripleC → TripleC
tripleAdd = C3.zipTriple C3._+C_

tripleNeg : TripleC → TripleC
tripleNeg = C3.mapTriple negC

tripleHalf : TripleC → TripleC
tripleHalf = C3.mapTriple (C3.scaleC ½)

forward2Triple : SixSignal → SixSignal
forward2Triple (pair a b) =
  pair (tripleAdd a b)
       (tripleAdd a (tripleNeg b))

inverse2Triple : SixSignal → SixSignal
inverse2Triple (pair a b) =
  pair (tripleHalf (tripleAdd a b))
       (tripleHalf (tripleAdd a (tripleNeg b)))

-- The following two proofs are literally the three independent
-- copies of the native two-point Cyclotomic3 rational transform.
sixC2RoundTrip : ∀ x → inverse2Triple (forward2Triple x) ≡ x
sixC2RoundTrip
  (pair (C3.triple a b c) (C3.triple d e f)) =
  pair-ext
    (C3.triple-ext
      (twoRoundTripCoordinateLeft a d)
      (twoRoundTripCoordinateLeft b e)
      (twoRoundTripCoordinateLeft c f))
    (C3.triple-ext
      (twoRoundTripCoordinateRight a d)
      (twoRoundTripCoordinateRight b e)
      (twoRoundTripCoordinateRight c f))
  where
  twoRoundTripCoordinateLeft : ∀ a b →
    C3.scaleC ½
      (C3._+C_
        (C3._+C_ a b)
        (C3._+C_ a (negC b))) ≡ a
  twoRoundTripCoordinateLeft (C3.cyc a b) (C3.cyc c d) =
    C3.cyc-ext Ring.solve-∀ Ring.solve-∀

  twoRoundTripCoordinateRight : ∀ a b →
    C3.scaleC ½
      (C3._+C_
        (C3._+C_ a b)
        (negC (C3._+C_ a (negC b)))) ≡ b
  twoRoundTripCoordinateRight (C3.cyc a b) (C3.cyc c d) =
    C3.cyc-ext Ring.solve-∀ Ring.solve-∀

sixC2ForwardInverse : ∀ x → forward2Triple (inverse2Triple x) ≡ x
sixC2ForwardInverse
  (pair (C3.triple a b c) (C3.triple d e f)) =
  pair-ext
    (C3.triple-ext
      (twoForwardInverseCoordinateLeft a d)
      (twoForwardInverseCoordinateLeft b e)
      (twoForwardInverseCoordinateLeft c f))
    (C3.triple-ext
      (twoForwardInverseCoordinateRight a d)
      (twoForwardInverseCoordinateRight b e)
      (twoForwardInverseCoordinateRight c f))
  where
  twoForwardInverseCoordinateLeft : ∀ a b →
    C3._+C_
      (C3.scaleC ½ (C3._+C_ a b))
      (C3.scaleC ½ (C3._+C_ a (negC b))) ≡ a
  twoForwardInverseCoordinateLeft (C3.cyc a b) (C3.cyc c d) =
    C3.cyc-ext Ring.solve-∀ Ring.solve-∀

  twoForwardInverseCoordinateRight : ∀ a b →
    C3._+C_
      (C3.scaleC ½ (C3._+C_ a b))
      (negC (C3.scaleC ½ (C3._+C_ a (negC b)))) ≡ b
  twoForwardInverseCoordinateRight (C3.cyc a b) (C3.cyc c d) =
    C3.cyc-ext Ring.solve-∀ Ring.solve-∀

-- Cartesian C2 x C3 transform; reuse the native C3 result, not
-- a postulated general Fourier inversion theorem.
forwardSix : SixSignal → SixSignal
forwardSix x = mapPair C3.forward1 (forward2Triple x)

inverseSix : SixSignal → SixSignal
inverseSix x = inverse2Triple (mapPair C3.inverse1 x)

threeC3RoundTrip : ∀ x →
  mapPair C3.inverse1 (mapPair C3.forward1 x) ≡ x
threeC3RoundTrip (pair a b) =
  pair-ext
    (C3.oneDimensionalFourierInversion a)
    (C3.oneDimensionalFourierInversion b)

threeC3ForwardInverse : ∀ x →
  mapPair C3.forward1 (mapPair C3.inverse1 x) ≡ x
threeC3ForwardInverse (pair a b) =
  pair-ext
    (C3.oneDimensionalFourierForwardInverse a)
    (C3.oneDimensionalFourierForwardInverse b)

sixFourierInversion : ∀ x → inverseSix (forwardSix x) ≡ x
sixFourierInversion x =
  trans
    (cong inverse2Triple (threeC3RoundTrip (forward2Triple x)))
    (sixC2RoundTrip x)

sixFourierForwardInverse : ∀ x → forwardSix (inverseSix x) ≡ x
sixFourierForwardInverse x =
  trans
    (cong (mapPair C3.forward1)
      (sixC2ForwardInverse (mapPair C3.inverse1 x)))
    (threeC3ForwardInverse x)

-- Actual C18 selected positions, using CRT C6 ~= C2 x C3.
selectedSixSamples :
  (Phase.Phase18 → C3.Cyclotomic3) → SixSignal
selectedSixSamples f =
  pair
    (C3.triple (f Phase.p18-0) (f Phase.p18-4) (f Phase.p18-2))
    (C3.triple (f Phase.p18-3) (f Phase.p18-1) (f Phase.p18-5))

reconstructSelectedSixSamples :
  (f : Phase.Phase18 → C3.Cyclotomic3) →
  inverseSix (forwardSix (selectedSixSamples f))
    ≡ selectedSixSamples f
reconstructSelectedSixSamples f = sixFourierInversion (selectedSixSamples f)
