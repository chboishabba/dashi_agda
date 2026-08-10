module DASHI.Physics.Closure.NSTriadKNComplex3RealityLawsRound35Exact where

------------------------------------------------------------------------
-- PRIMARY SOURCES / CONTEXT
--
-- Author: Jean Leray.
-- Title: "Sur le mouvement d'un liquide visqueux emplissant l'espace".
-- DOI: 10.1007/BF02547354.
--
-- Author: Roger Temam.
-- Title: "Navier-Stokes Equations: Theory and Numerical Analysis".
-- DOI: 10.1090/chel/343.
--
-- DASHI CONTRIBUTION
--
-- Complete the local Fourier-reality algebra exposed by
-- `CorrectComplex3RealityLaws`.  Round 35 first derives inverse-square
-- evenness from the existing `ModeInverseSquare` geometry.  Here we use that
-- theorem to prove the two remaining facts rather than accepting them as
-- audit fields:
--
--   P_{-k} v = P_k v,
--   P_k(conjugate v) = conjugate(P_k v).
--
-- The first identity uses the two sign reversals in
--   (k dot v) k,
-- while the second uses that the wavevector and |k|^-2 are real.  No
-- continuum estimate or reality assumption on `v` enters these identities.
------------------------------------------------------------------------

open import Agda.Builtin.Bool using (Bool; true; false)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Relation.Binary.PropositionalEquality using
  (cong; cong₂; sym; trans; module ≡-Reasoning)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAdditiveLaws as Additive
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianScalingLaws as Scaling
import DASHI.Physics.Closure.NSTriadKNComplex3RealityPhaseAudit as Reality
import DASHI.Physics.Closure.NSTriadKNModeInverseSquareRealityRound35Exact as InverseReality

bilinearDotNegateLeft :
  ∀ {r} {F : C3.RealField r}
    (u v : C3.Complex3 F) →
  C3.bilinearDot3 (C3.complex3Negate u) v
  ≡ C3.complexNegate (C3.bilinearDot3 u v)
bilinearDotNegateLeft u v =
  trans
    (Algebra.bilinearDotCommutative (C3.complex3Negate u) v)
    (trans
      (Algebra.bilinearDotNegateRight v u)
      (cong C3.complexNegate (Algebra.bilinearDotCommutative v u)))

complexDoubleNegateMultiply :
  ∀ {r} {F : C3.RealField r}
    (a b : C3.Complex F) →
  C3.complexMultiply (C3.complexNegate a) (C3.complexNegate b)
  ≡ C3.complexMultiply a b
complexDoubleNegateMultiply a b =
  trans
    (Algebra.complexNegateMultiplyLeft a (C3.complexNegate b))
    (trans
      (cong C3.complexNegate
        (Algebra.complexNegateMultiplyRight a b))
      (Algebra.complexNegateInvolutive (C3.complexMultiply a b)))

complex3ScaleDoubleNegate :
  ∀ {r} {F : C3.RealField r}
    (scalar : C3.Complex F) (vector : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexNegate scalar)
    (C3.complex3Negate vector)
  ≡ C3.complex3Scale scalar vector
complex3ScaleDoubleNegate scalar (C3.complex3 vx vy vz) =
  Algebra.complex3Ext
    (complexDoubleNegateMultiply scalar vx)
    (complexDoubleNegateMultiply scalar vy)
    (complexDoubleNegateMultiply scalar vz)

complex3ConjugateSubtract :
  ∀ {r} {F : C3.RealField r}
    (left right : C3.Complex3 F) →
  C3.complex3Conjugate (C3.complex3Subtract left right)
  ≡ C3.complex3Subtract
      (C3.complex3Conjugate left)
      (C3.complex3Conjugate right)
complex3ConjugateSubtract left right =
  trans
    (Additive.complex3ConjugateAdd left (C3.complex3Negate right))
    (cong
      (C3.complex3Add (C3.complex3Conjugate left))
      (Additive.complex3ConjugateNegate right))

modeDotConjugate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E k)
    (C3.complex3Conjugate value)
  ≡ C3.complexConjugate
      (C3.bilinearDot3 (C3.modeVector E k) value)
modeDotConjugate E k value =
  trans
    (cong
      (λ first → C3.bilinearDot3 first (C3.complex3Conjugate value))
      (sym (C3.modeVectorConjugate E k)))
    (Algebra.bilinearDotConjugate (C3.modeVector E k) value)

realCoefficientConjugate :
  ∀ {r} {F : C3.RealField r}
    (coefficient : C3.Carrier F)
    (scalar : C3.Complex F) →
  C3.complexConjugate
    (C3.complexMultiply (C3.realEmbed F coefficient) scalar)
  ≡ C3.complexMultiply
      (C3.realEmbed F coefficient)
      (C3.complexConjugate scalar)
realCoefficientConjugate {F = F} coefficient scalar =
  trans
    (Algebra.complexConjugateMultiply
      (C3.realEmbed F coefficient) scalar)
    (cong
      (λ realPart →
        C3.complexMultiply realPart (C3.complexConjugate scalar))
      (C3.realEmbedConjugate F coefficient))

lerayCorrectionModeEven :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I (Z3.negateMode k)))
      (C3.bilinearDot3 (C3.modeVector E (Z3.negateMode k)) value))
    (C3.modeVector E (Z3.negateMode k))
  ≡
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.bilinearDot3 (C3.modeVector E k) value))
    (C3.modeVector E k)
lerayCorrectionModeEven {F = F} E I k value =
  let
    inverse = C3.inverseNormSquared I k
    wave = C3.modeVector E k
    pairing = C3.bilinearDot3 wave value

    scalarEven :
      C3.complexMultiply
        (C3.realEmbed F (C3.inverseNormSquared I (Z3.negateMode k)))
        (C3.bilinearDot3 (C3.modeVector E (Z3.negateMode k)) value)
      ≡ C3.complexNegate
          (C3.complexMultiply (C3.realEmbed F inverse) pairing)
    scalarEven =
      trans
        (cong₂ C3.complexMultiply
          (cong (C3.realEmbed F)
            (InverseReality.inverseNormSquaredEven E I k))
          (trans
            (cong
              (λ selectedWave → C3.bilinearDot3 selectedWave value)
              (C3.modeVectorNegation E k))
            (bilinearDotNegateLeft wave value)))
        (Algebra.complexNegateMultiplyRight
          (C3.realEmbed F inverse) pairing)
  in
  trans
    (cong₂ C3.complex3Scale
      scalarEven
      (C3.modeVectorNegation E k))
    (complex3ScaleDoubleNegate
      (C3.complexMultiply (C3.realEmbed F inverse) pairing)
      wave)

lerayProjectModeEven :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I (Z3.negateMode k) value
  ≡ C3.lerayProject3 E I k value
lerayProjectModeEven E I k value =
  cong (C3.complex3Subtract value)
    (lerayCorrectionModeEven E I k value)

lerayCorrectionConjugate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.complex3Conjugate
    (C3.complex3Scale
      (C3.complexMultiply
        (C3.realEmbed F (C3.inverseNormSquared I k))
        (C3.bilinearDot3 (C3.modeVector E k) value))
      (C3.modeVector E k))
  ≡
  C3.complex3Scale
    (C3.complexMultiply
      (C3.realEmbed F (C3.inverseNormSquared I k))
      (C3.bilinearDot3
        (C3.modeVector E k)
        (C3.complex3Conjugate value)))
    (C3.modeVector E k)
lerayCorrectionConjugate {F = F} E I k value =
  let
    inverse = C3.inverseNormSquared I k
    pairing = C3.bilinearDot3 (C3.modeVector E k) value
  in
  trans
    (Scaling.complex3ConjugateScale
      (C3.complexMultiply (C3.realEmbed F inverse) pairing)
      (C3.modeVector E k))
    (cong₂ C3.complex3Scale
      (trans
        (realCoefficientConjugate inverse pairing)
        (cong
          (C3.complexMultiply (C3.realEmbed F inverse))
          (sym (modeDotConjugate E k value))))
      (C3.modeVectorConjugate E k))

lerayProjectConjugation :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E)
    (k : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.lerayProject3 E I k (C3.complex3Conjugate value)
  ≡ C3.complex3Conjugate (C3.lerayProject3 E I k value)
lerayProjectConjugation E I k value =
  sym
    (trans
      (complex3ConjugateSubtract value correction)
      (cong
        (C3.complex3Subtract (C3.complex3Conjugate value))
        (lerayCorrectionConjugate E I k value)))
  where
  correction =
    C3.complex3Scale
      (C3.complexMultiply
        (C3.realEmbed _ (C3.inverseNormSquared I k))
        (C3.bilinearDot3 (C3.modeVector E k) value))
      (C3.modeVector E k)

canonicalCorrectComplex3RealityLaws :
  ∀ {r} (F : C3.RealField r)
    (E : C3.IntegerEmbedding F)
    (I : C3.ModeInverseSquare F E) →
  Reality.CorrectComplex3RealityLaws F E I
canonicalCorrectComplex3RealityLaws F E I = record
  { Reality.CorrectComplex3RealityLaws.inverseNormEven =
      InverseReality.inverseNormSquaredEven E I
  ; Reality.CorrectComplex3RealityLaws.lerayModeEven =
      lerayProjectModeEven E I
  ; Reality.CorrectComplex3RealityLaws.lerayConjugation =
      lerayProjectConjugation E I
  }

complex3RealityLawsConstructed : Bool
complex3RealityLawsConstructed = true

complex3RealityLawsConstructedIsTrue :
  complex3RealityLawsConstructed ≡ true
complex3RealityLawsConstructedIsTrue = refl
