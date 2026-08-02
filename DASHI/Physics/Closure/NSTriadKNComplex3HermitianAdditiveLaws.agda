module DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Additive, negative, and subtractive Hermitian laws for the exact
-- Stage-3 C3 carrier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; these are repository-original consequences of the
-- exact RealField, complex, C3, and Hermitian scaling definitions.
-- Uses: complex conjugation over addition/negation, complex multiplication
-- associativity, bilinear-dot additivity, and the scalar -1 action.
-- Relationship: supplies the pairing laws needed to move the rank-one Leray
-- correction across a Hermitian pairing without adding any analytic norm or
-- order assumptions.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling

minusOne : ∀ {r} (F : C3.RealField r) → C3.Complex F
minusOne F = C3.complexNegate (C3.complexOne F)

realMinusOneMultiply :
  ∀ {r} (F : C3.RealField r) (value : C3.Carrier F) →
  C3.multiply F (C3.negate F (C3.one F)) value
  ≡ C3.negate F value
realMinusOneMultiply F value =
  trans
    (sym (Algebra.realNegateMultiplyLeft F (C3.one F) value))
    (cong (C3.negate F) (C3.multiplyOneLeft F value))

complexMultiplyMinusOneLeft :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexMultiply (minusOne F) value ≡ C3.complexNegate value
complexMultiplyMinusOneLeft {F = F} (C3.complex real imaginary)
  rewrite C3.negateZero F
        | Algebra.realMultiplyZeroLeft F real
        | Algebra.realMultiplyZeroLeft F imaginary
        | C3.negateZero F
        | realMinusOneMultiply F real
        | realMinusOneMultiply F imaginary
        | Algebra.realAddZeroRight F (C3.negate F real)
        | Algebra.realAddZeroRight F (C3.negate F imaginary) = refl

complexMultiplyMinusOneRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexMultiply value (minusOne F) ≡ C3.complexNegate value
complexMultiplyMinusOneRight value =
  trans
    (Algebra.complexMultiplyCommutative value (minusOne _))
    (complexMultiplyMinusOneLeft value)

complexConjugateMinusOne :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (minusOne F) ≡ minusOne F
complexConjugateMinusOne F
  rewrite C3.negateZero F = refl

complexAddInverseRight :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexAdd value (C3.complexNegate value) ≡ C3.complexZero F
complexAddInverseRight {F = F} (C3.complex real imaginary)
  rewrite Algebra.realAddInverseRight F real
        | Algebra.realAddInverseRight F imaginary = refl

complexSubtractSelf :
  ∀ {r} {F : C3.RealField r} (value : C3.Complex F) →
  C3.complexSubtract value value ≡ C3.complexZero F
complexSubtractSelf = complexAddInverseRight

complex3ConjugateAdd :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.complex3Conjugate (C3.complex3Add u v)
  ≡ C3.complex3Add (C3.complex3Conjugate u) (C3.complex3Conjugate v)
complex3ConjugateAdd
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateAdd ux vx
        | Hermitian.complexConjugateAdd uy vy
        | Hermitian.complexConjugateAdd uz vz = refl

complex3ConjugateNegate :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Conjugate (C3.complex3Negate value)
  ≡ C3.complex3Negate (C3.complex3Conjugate value)
complex3ConjugateNegate (C3.complex3 vx vy vz)
  rewrite Hermitian.complexConjugateNegate vx
        | Hermitian.complexConjugateNegate vy
        | Hermitian.complexConjugateNegate vz = refl

complex3ScaleMinusOne :
  ∀ {r} {F : C3.RealField r}
    (value : C3.Complex3 F) →
  C3.complex3Scale (minusOne F) value ≡ C3.complex3Negate value
complex3ScaleMinusOne (C3.complex3 vx vy vz)
  rewrite complexMultiplyMinusOneLeft vx
        | complexMultiplyMinusOneLeft vy
        | complexMultiplyMinusOneLeft vz = refl

bilinearDot3LeftAdd :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.bilinearDot3 (C3.complex3Add u v) w
  ≡ C3.complexAdd (C3.bilinearDot3 u w) (C3.bilinearDot3 v w)
bilinearDot3LeftAdd u v w =
  trans
    (Algebra.bilinearDot3Commutative (C3.complex3Add u v) w)
    (trans
      (Algebra.bilinearDot3RightAdd w u v)
      (Algebra.cong₂ C3.complexAdd
        (Algebra.bilinearDot3Commutative w u)
        (Algebra.bilinearDot3Commutative w v)))

hermitianPairingAddLeft :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Add u v) w
  ≡ C3.complexAdd
      (C3.hermitianPairing3 u w)
      (C3.hermitianPairing3 v w)
hermitianPairingAddLeft u v w =
  trans
    (cong (λ first → C3.bilinearDot3 first w)
      (complex3ConjugateAdd u v))
    (bilinearDot3LeftAdd
      (C3.complex3Conjugate u)
      (C3.complex3Conjugate v)
      w)

hermitianPairingAddRight :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Add v w)
  ≡ C3.complexAdd
      (C3.hermitianPairing3 u v)
      (C3.hermitianPairing3 u w)
hermitianPairingAddRight u v w =
  Algebra.bilinearDot3RightAdd (C3.complex3Conjugate u) v w

hermitianPairingNegateLeft :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Negate u) v
  ≡ C3.complexNegate (C3.hermitianPairing3 u v)
hermitianPairingNegateLeft {F = F} u v =
  trans
    (cong (λ first → C3.hermitianPairing3 first v)
      (sym (complex3ScaleMinusOne u)))
    (trans
      (Scaling.hermitianPairingScaleLeft (minusOne F) u v)
      (trans
        (cong
          (λ scalar → C3.complexMultiply scalar
            (C3.hermitianPairing3 u v))
          (complexConjugateMinusOne F))
        (complexMultiplyMinusOneLeft (C3.hermitianPairing3 u v))))

hermitianPairingNegateRight :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Negate v)
  ≡ C3.complexNegate (C3.hermitianPairing3 u v)
hermitianPairingNegateRight {F = F} u v =
  trans
    (cong (C3.hermitianPairing3 u)
      (sym (complex3ScaleMinusOne v)))
    (trans
      (Scaling.hermitianPairingScaleRight (minusOne F) u v)
      (complexMultiplyMinusOneLeft (C3.hermitianPairing3 u v)))

hermitianPairingSubtractLeft :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.complex3Subtract u v) w
  ≡ C3.complexSubtract
      (C3.hermitianPairing3 u w)
      (C3.hermitianPairing3 v w)
hermitianPairingSubtractLeft u v w =
  trans
    (hermitianPairingAddLeft u (C3.complex3Negate v) w)
    (cong (C3.complexAdd (C3.hermitianPairing3 u w))
      (hermitianPairingNegateLeft v w))

hermitianPairingSubtractRight :
  ∀ {r} {F : C3.RealField r}
    (u v w : C3.Complex3 F) →
  C3.hermitianPairing3 u (C3.complex3Subtract v w)
  ≡ C3.complexSubtract
      (C3.hermitianPairing3 u v)
      (C3.hermitianPairing3 u w)
hermitianPairingSubtractRight u v w =
  trans
    (hermitianPairingAddRight u v (C3.complex3Negate w))
    (cong (C3.complexAdd (C3.hermitianPairing3 u v))
      (hermitianPairingNegateRight u w))

hermitianAdditiveAndSubtractiveLawsClosed : Bool
hermitianAdditiveAndSubtractiveLawsClosed = true

hermitianAdditiveAndSubtractiveLawsClosedIsTrue :
  hermitianAdditiveAndSubtractiveLawsClosed ≡ true
hermitianAdditiveAndSubtractiveLawsClosedIsTrue = refl
