module DASHI.Physics.Closure.NSTriadKNComplex3EuclideanSelfPairing where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Exact Euclidean squared norm from the real Hermitian self-pairing
-- on the Stage-3 C3 carrier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; this is a repository-original coordinate theorem.
-- Uses: the literal complex conjugation and multiplication definitions, the
-- derived negated-product law, and the convention <u,v> = conjugate(u) dot v.
-- Relationship: proves Re <v,v> = ||v||^2 algebraically over every repository
-- RealField.  Positivity and zero-norm separation still belong to the ordered
-- analytic instance rather than the algebraic field interface.
------------------------------------------------------------------------

open import Agda.Primitive using (Level)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; trans; sym)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNOrderedEuclideanL2Carrier as Euclidean

complexSelfProductRealPart :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.real
    (C3.complexMultiply (C3.complexConjugate value) value)
  ≡ Euclidean.complexModulusSquared value
complexSelfProductRealPart {F = F} (C3.complex real imaginary) =
  cong (C3.add F (C3.multiply F real real)) imaginarySquare
  where
    imaginarySquare :
      C3.negate F
        (C3.multiply F (C3.negate F imaginary) imaginary)
      ≡ C3.multiply F imaginary imaginary
    imaginarySquare =
      trans
        (cong (C3.negate F)
          (sym (Algebra.realNegateMultiplyLeft F imaginary imaginary)))
        (C3.negateInvolutive F (C3.multiply F imaginary imaginary))

complex3SelfPairingRealPartIsNormSquared :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex3 F) →
  C3.real (C3.hermitianPairing3 value value)
  ≡ Euclidean.complex3NormSquared value
complex3SelfPairingRealPartIsNormSquared
  (C3.complex3 xValue yValue zValue)
  rewrite complexSelfProductRealPart xValue
        | complexSelfProductRealPart yValue
        | complexSelfProductRealPart zValue = refl

complex3EuclideanSelfPairingClosed : Bool
complex3EuclideanSelfPairingClosed = true

complex3EuclideanSelfPairingClosedIsTrue :
  complex3EuclideanSelfPairingClosed ≡ true
complex3EuclideanSelfPairingClosedIsTrue = refl

complex3EuclideanPositivityClosed : Bool
complex3EuclideanPositivityClosed = false

complex3EuclideanPositivityClosedIsFalse :
  complex3EuclideanPositivityClosed ≡ false
complex3EuclideanPositivityClosedIsFalse = refl
