module DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram where

------------------------------------------------------------------------
-- PROVENANCE
-- Authors: DASHI repository contributors.
-- Title: "Concrete complex conjugation, Hermitian symmetry, and scaling
-- boundary for the Stage-3 C3 carrier".
-- Venue/year: DASHI formal development, 2026.
-- DOI: not applicable; these are repository-original consequences of the
-- exact RealField and C3 definitions.
-- Uses: the literal complex arithmetic, coordinatewise conjugation,
-- bilinear dot product, real lattice embedding, and Hermitian convention
-- <u,v> = conjugate(u) dot v.
-- Relationship: closes the conjugation, zero/one, real-mode, and Hermitian
-- conjugate-symmetry laws.  Complex multiplication associativity and the two
-- Hermitian scale laws remain an explicit cutset rather than assumed facts.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3AlgebraLaws as Algebra

complexConjugateZero :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexZero F) ≡ C3.complexZero F
complexConjugateZero F rewrite C3.negateZero F = refl

complexConjugateOne :
  ∀ {r} (F : C3.RealField r) →
  C3.complexConjugate (C3.complexOne F) ≡ C3.complexOne F
complexConjugateOne F rewrite C3.negateZero F = refl

complexNegateZero :
  ∀ {r} (F : C3.RealField r) →
  C3.complexNegate (C3.complexZero F) ≡ C3.complexZero F
complexNegateZero F rewrite C3.negateZero F = refl

complexMultiplyZeroLeft :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexMultiply (C3.complexZero F) z ≡ C3.complexZero F
complexMultiplyZeroLeft {F = F} (C3.complex real imaginary)
  rewrite Algebra.realMultiplyZeroLeft F real
        | Algebra.realMultiplyZeroLeft F imaginary
        | C3.negateZero F
        | C3.addZeroLeft F (C3.zero F) = refl

complexMultiplyZeroRight :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexMultiply z (C3.complexZero F) ≡ C3.complexZero F
complexMultiplyZeroRight z =
  trans
    (Algebra.complexMultiplyCommutative z (C3.complexZero _))
    (complexMultiplyZeroLeft z)

complexMultiplyOneLeft :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexMultiply (C3.complexOne F) z ≡ z
complexMultiplyOneLeft {F = F} (C3.complex real imaginary)
  rewrite C3.multiplyOneLeft F real
        | C3.multiplyOneLeft F imaginary
        | Algebra.realMultiplyZeroLeft F real
        | Algebra.realMultiplyZeroLeft F imaginary
        | C3.negateZero F
        | Algebra.realAddZeroRight F real
        | Algebra.realAddZeroRight F imaginary = refl

complexMultiplyOneRight :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexMultiply z (C3.complexOne F) ≡ z
complexMultiplyOneRight z =
  trans
    (Algebra.complexMultiplyCommutative z (C3.complexOne _))
    (complexMultiplyOneLeft z)

complexConjugateAdd :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexConjugate (C3.complexAdd a b)
  ≡ C3.complexAdd (C3.complexConjugate a) (C3.complexConjugate b)
complexConjugateAdd {F = F}
  (C3.complex ar ai) (C3.complex br bi)
  rewrite Algebra.realNegateAdd F ai bi = refl

complexConjugateNegate :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexConjugate (C3.complexNegate z)
  ≡ C3.complexNegate (C3.complexConjugate z)
complexConjugateNegate (C3.complex real imaginary) = refl

complexRealPartConjugateInvariant :
  ∀ {r} {F : C3.RealField r} (z : C3.Complex F) →
  C3.complexRealPart (C3.complexConjugate z)
  ≡ C3.complexRealPart z
complexRealPartConjugateInvariant (C3.complex real imaginary) = refl

complexConjugateMultiply :
  ∀ {r} {F : C3.RealField r} (a b : C3.Complex F) →
  C3.complexConjugate (C3.complexMultiply a b)
  ≡ C3.complexMultiply (C3.complexConjugate a) (C3.complexConjugate b)
complexConjugateMultiply {F = F}
  (C3.complex ar ai) (C3.complex br bi) =
  Algebra.cong₂ C3.complex realCoordinate imaginaryCoordinate
  where
    realCoordinate :
      C3.add F
        (C3.multiply F ar br)
        (C3.negate F (C3.multiply F ai bi))
      ≡
      C3.add F
        (C3.multiply F ar br)
        (C3.negate F
          (C3.multiply F (C3.negate F ai) (C3.negate F bi)))
    realCoordinate =
      cong (C3.add F (C3.multiply F ar br))
        (cong (C3.negate F)
          (sym (Algebra.realDoubleNegateProduct F ai bi)))

    imaginaryCoordinate :
      C3.negate F
        (C3.add F
          (C3.multiply F ar bi)
          (C3.multiply F ai br))
      ≡
      C3.add F
        (C3.multiply F ar (C3.negate F bi))
        (C3.multiply F (C3.negate F ai) br)
    imaginaryCoordinate =
      trans
        (Algebra.realNegateAdd F
          (C3.multiply F ar bi)
          (C3.multiply F ai br))
        (Algebra.cong₂ (C3.add F)
          (Algebra.realNegateMultiplyRight F ar bi)
          (Algebra.realNegateMultiplyLeft F ai br))

complex3AddZeroRight :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Add v (C3.complex3Zero F) ≡ v
complex3AddZeroRight (C3.complex3 vx vy vz)
  rewrite Algebra.complexAddZeroRight vx
        | Algebra.complexAddZeroRight vy
        | Algebra.complexAddZeroRight vz = refl

complex3NegateZero :
  ∀ {r} (F : C3.RealField r) →
  C3.complex3Negate (C3.complex3Zero F) ≡ C3.complex3Zero F
complex3NegateZero F
  rewrite complexNegateZero F = refl

complex3SubtractZero :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Subtract v (C3.complex3Zero F) ≡ v
complex3SubtractZero {F = F} v
  rewrite complex3NegateZero F
        | complex3AddZeroRight v = refl

complex3ScaleZero :
  ∀ {r} {F : C3.RealField r} (v : C3.Complex3 F) →
  C3.complex3Scale (C3.complexZero F) v ≡ C3.complex3Zero F
complex3ScaleZero (C3.complex3 vx vy vz)
  rewrite complexMultiplyZeroLeft vx
        | complexMultiplyZeroLeft vy
        | complexMultiplyZeroLeft vz = refl

bilinearDot3Conjugate :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.complexConjugate (C3.bilinearDot3 u v)
  ≡ C3.bilinearDot3 (C3.complex3Conjugate u) (C3.complex3Conjugate v)
bilinearDot3Conjugate
  (C3.complex3 ux uy uz) (C3.complex3 vx vy vz)
  rewrite complexConjugateAdd
            (C3.complexAdd
              (C3.complexMultiply ux vx)
              (C3.complexMultiply uy vy))
            (C3.complexMultiply uz vz)
        | complexConjugateAdd
            (C3.complexMultiply ux vx)
            (C3.complexMultiply uy vy)
        | complexConjugateMultiply ux vx
        | complexConjugateMultiply uy vy
        | complexConjugateMultiply uz vz = refl

hermitianPairingConjugateSymmetric :
  ∀ {r} {F : C3.RealField r} (u v : C3.Complex3 F) →
  C3.complexConjugate (C3.hermitianPairing3 u v)
  ≡ C3.hermitianPairing3 v u
hermitianPairingConjugateSymmetric u v =
  trans
    (bilinearDot3Conjugate (C3.complex3Conjugate u) v)
    (trans
      (cong
        (λ first → C3.bilinearDot3 first (C3.complex3Conjugate v))
        (C3.complex3ConjugateInvolutive u))
      (Algebra.bilinearDot3Commutative u (C3.complex3Conjugate v)))

realModePairingIsBilinear :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (v : C3.Complex3 F) →
  C3.hermitianPairing3 (C3.modeVector E k) v
  ≡ C3.bilinearDot3 (C3.modeVector E k) v
realModePairingIsBilinear E k v =
  cong (λ first → C3.bilinearDot3 first v)
    (C3.modeVectorConjugate E k)

record HermitianScalingCutset
    {r : Level} (F : C3.RealField r) : Set (lsuc r) where
  field
    complexMultiplyAssociative : ∀ a b c →
      C3.complexMultiply (C3.complexMultiply a b) c
      ≡ C3.complexMultiply a (C3.complexMultiply b c)

    hermitianPairingScaleLeft : ∀ scalar u v →
      C3.hermitianPairing3 (C3.complex3Scale scalar u) v
      ≡ C3.complexMultiply
          (C3.complexConjugate scalar)
          (C3.hermitianPairing3 u v)

    hermitianPairingScaleRight : ∀ scalar u v →
      C3.hermitianPairing3 u (C3.complex3Scale scalar v)
      ≡ C3.complexMultiply scalar (C3.hermitianPairing3 u v)

open HermitianScalingCutset public

complexConjugationAndHermitianSymmetryClosed : Bool
complexConjugationAndHermitianSymmetryClosed = true

complexConjugationAndHermitianSymmetryClosedIsTrue :
  complexConjugationAndHermitianSymmetryClosed ≡ true
complexConjugationAndHermitianSymmetryClosedIsTrue = refl

hermitianScalingLawsClosed : Bool
hermitianScalingLawsClosed = false

hermitianScalingLawsClosedIsFalse : hermitianScalingLawsClosed ≡ false
hermitianScalingLawsClosedIsFalse = refl
