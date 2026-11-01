module DASHI.Moonshine.Monster3BCyclotomicNonzeroInverseExact where

------------------------------------------------------------------------
-- CONSTRUCTIVE INVERSION IN Q(zeta_3) FROM A NONZERO NORM RECEIPT
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using ([]; _∷_)
open import Data.Rational.Base as ℚ using
  (ℚ; 0ℚ; 1ℚ; _+_; _*_; 1/_; NonZero)
import Data.Rational.Properties as ℚP
open import Data.Rational.Tactic.RingSolver using (solve)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Moonshine.C3CyclotomicAmplitudeAlgebraExact as C3
import DASHI.Moonshine.Monster3BCyclotomicLinearAlgebraExact as L

record NonzeroCyclotomicAmplitude : Set where
  constructor nonzeroCyclotomicAmplitude
  field
    amplitude : C3.Cyclotomic3
    normNonzero : NonZero (C3.norm amplitude)
open NonzeroCyclotomicAmplitude public

normInverse : NonzeroCyclotomicAmplitude → ℚ
normInverse witness =
  let instance nz = normNonzero witness
  in 1/ C3.norm (amplitude witness)

inverse : NonzeroCyclotomicAmplitude → C3.Cyclotomic3
inverse witness =
  L.scale (normInverse witness) (C3.conjugate (amplitude witness))

multiplyScaleRight :
  (a : C3.Cyclotomic3) → (r : ℚ) → (b : C3.Cyclotomic3) →
  C3.multiply a (L.scale r b) ≡ L.scale r (C3.multiply a b)
multiplyScaleRight
  (C3.cyclotomic3 a b) r (C3.cyclotomic3 c d) =
  C3.cyclotomic3Ext
    (solve (a ∷ b ∷ c ∷ d ∷ r ∷ []))
    (solve (a ∷ b ∷ c ∷ d ∷ r ∷ []))

scaleEmbeddedNormToOne : (witness : NonzeroCyclotomicAmplitude) →
  L.scale (normInverse witness)
    (C3.embedRational (C3.norm (amplitude witness)))
  ≡ C3.one
scaleEmbeddedNormToOne witness =
  let
    n = C3.norm (amplitude witness)
    instance nz = normNonzero witness
    inverseRight : n * (1/ n) ≡ 1ℚ
    inverseRight = ℚP.*-inverseʳ n
  in
  C3.cyclotomic3Ext
    (trans (ℚP.*-comm (1/ n) n) inverseRight)
    refl

rightInverse : (witness : NonzeroCyclotomicAmplitude) →
  C3.multiply (amplitude witness) (inverse witness) ≡ C3.one
rightInverse witness =
  trans
    (multiplyScaleRight
      (amplitude witness) (normInverse witness)
      (C3.conjugate (amplitude witness)))
    (trans
      (cong (L.scale (normInverse witness))
        (C3.multiplyByConjugateLandsOnNorm (amplitude witness)))
      (scaleEmbeddedNormToOne witness))

record CyclotomicInverseBoundary : Set where
  constructor cyclotomicInverseBoundary
  field
    normQualifiedNonzeroCarrierConstructed : Bool
    conjugateOverNormInverseConstructed : Bool
    rightInverseProved : Bool
open CyclotomicInverseBoundary public

canonicalCyclotomicInverseBoundary : CyclotomicInverseBoundary
canonicalCyclotomicInverseBoundary = cyclotomicInverseBoundary true true true
