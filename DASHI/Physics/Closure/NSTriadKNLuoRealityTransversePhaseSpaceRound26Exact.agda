module DASHI.Physics.Closure.NSTriadKNLuoRealityTransversePhaseSpaceRound26Exact where

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
-- A finite Galerkin state is represented by positive-orbit coefficients with
-- transversality evidence.  The negative mode and coefficient are not supplied
-- independently:
--
--   mode(-)  = - mode(+),
--   value(-) = conjugate(value(+)).
--
-- Reality is therefore built into reconstruction.  Round 26 now also proves
-- transversality of the reconstructed negative coefficient on the repository's
-- exact Complex3 carrier.  The proof uses only:
--
-- * mode-vector negation and reality;
-- * commutativity and negation of the bilinear dot product;
-- * conjugation of the bilinear dot product;
-- * conjugation and negation of zero.
--
-- No continuum analytic assumption is needed for this algebraic invariant.
------------------------------------------------------------------------

open import Agda.Primitive using (Level; lsuc)
open import Agda.Builtin.Equality using (_≡_; refl)
open import Agda.Builtin.List using (List; []; _∷_)
open import Relation.Binary.PropositionalEquality using (cong; sym; trans)

import DASHI.Physics.Closure.NSIntegerFourierLattice as Z3
import DASHI.Physics.Closure.NSTriadKNComplex3ExactCarrier as C3
import DASHI.Physics.Closure.NSTriadKNComplex3FieldAlgebra as Algebra
import DASHI.Physics.Closure.NSTriadKNComplex3HermitianAlgebraProgram as Hermitian

record TransverseModeCoefficient
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor transverse-mode-coefficient
  field
    coefficientMode : Z3.FourierMode
    coefficientValue : C3.Complex3 F
    transverse :
      C3.bilinearDot3
        (C3.modeVector E coefficientMode)
        coefficientValue
      ≡ C3.complexZero F

open TransverseModeCoefficient public

reconstructedNegativeMode :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  TransverseModeCoefficient F E → Z3.FourierMode
reconstructedNegativeMode coefficient =
  Z3.negateMode (coefficientMode coefficient)

reconstructedNegativeValue :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  TransverseModeCoefficient F E → C3.Complex3 F
reconstructedNegativeValue coefficient =
  C3.complex3Conjugate (coefficientValue coefficient)

negativeModeIsNegation :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : TransverseModeCoefficient F E) →
  reconstructedNegativeMode coefficient
  ≡ Z3.negateMode (coefficientMode coefficient)
negativeModeIsNegation coefficient = refl

negativeValueIsConjugate :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F}
    (coefficient : TransverseModeCoefficient F E) →
  reconstructedNegativeValue coefficient
  ≡ C3.complex3Conjugate (coefficientValue coefficient)
negativeValueIsConjugate coefficient = refl

record ConjugateTransversalityLaw
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set (lsuc r) where
  field
    conjugatePreservesTransverse :
      ∀ mode value →
      C3.bilinearDot3 (C3.modeVector E mode) value
        ≡ C3.complexZero F →
      C3.bilinearDot3
        (C3.modeVector E (Z3.negateMode mode))
        (C3.complex3Conjugate value)
        ≡ C3.complexZero F

open ConjugateTransversalityLaw public

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
      (cong C3.complexNegate
        (Algebra.bilinearDotCommutative v u)))

modeDotConjugateValueIsConjugate :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F)
    (mode : Z3.FourierMode)
    (value : C3.Complex3 F) →
  C3.bilinearDot3
    (C3.modeVector E mode)
    (C3.complex3Conjugate value)
  ≡
  C3.complexConjugate
    (C3.bilinearDot3 (C3.modeVector E mode) value)
modeDotConjugateValueIsConjugate E mode value =
  trans
    (cong
      (λ first → C3.bilinearDot3 first (C3.complex3Conjugate value))
      (sym (C3.modeVectorConjugate E mode)))
    (sym
      (Hermitian.bilinearDot3Conjugate
        (C3.modeVector E mode)
        value))

canonicalConjugatePreservesTransverse :
  ∀ {r} {F : C3.RealField r}
    (E : C3.IntegerEmbedding F) →
  ∀ mode value →
  C3.bilinearDot3 (C3.modeVector E mode) value
    ≡ C3.complexZero F →
  C3.bilinearDot3
    (C3.modeVector E (Z3.negateMode mode))
    (C3.complex3Conjugate value)
    ≡ C3.complexZero F
canonicalConjugatePreservesTransverse {F = F} E mode value transverse =
  trans
    (cong
      (λ first → C3.bilinearDot3 first (C3.complex3Conjugate value))
      (C3.modeVectorNegation E mode))
    (trans
      (bilinearDotNegateLeft
        (C3.modeVector E mode)
        (C3.complex3Conjugate value))
      (trans
        (cong C3.complexNegate
          (trans
            (modeDotConjugateValueIsConjugate E mode value)
            (trans
              (cong C3.complexConjugate transverse)
              (Hermitian.complexConjugateZero F))))
        (Hermitian.complexNegateZero F)))

canonicalConjugateTransversalityLaw :
  ∀ {r} (F : C3.RealField r) (E : C3.IntegerEmbedding F) →
  ConjugateTransversalityLaw F E
canonicalConjugateTransversalityLaw F E = record
  { conjugatePreservesTransverse =
      canonicalConjugatePreservesTransverse E
  }

reconstructedNegativeIsTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  (law : ConjugateTransversalityLaw F E) →
  (coefficient : TransverseModeCoefficient F E) →
  C3.bilinearDot3
    (C3.modeVector E (reconstructedNegativeMode coefficient))
    (reconstructedNegativeValue coefficient)
  ≡ C3.complexZero F
reconstructedNegativeIsTransverse law coefficient =
  conjugatePreservesTransverse law
    (coefficientMode coefficient)
    (coefficientValue coefficient)
    (transverse coefficient)

canonicalReconstructedNegativeIsTransverse :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  (coefficient : TransverseModeCoefficient F E) →
  C3.bilinearDot3
    (C3.modeVector E (reconstructedNegativeMode coefficient))
    (reconstructedNegativeValue coefficient)
  ≡ C3.complexZero F
canonicalReconstructedNegativeIsTransverse {F = F} {E = E} coefficient =
  reconstructedNegativeIsTransverse
    (canonicalConjugateTransversalityLaw F E)
    coefficient

record LiteralRealGalerkinPhaseSpace
    {r : Level}
    (F : C3.RealField r)
    (E : C3.IntegerEmbedding F) : Set r where
  constructor literal-real-galerkin-phase-space
  field
    positiveOrbitCoefficients : List (TransverseModeCoefficient F E)

open LiteralRealGalerkinPhaseSpace public

reconstructedModes :
  ∀ {r} {F : C3.RealField r} {E : C3.IntegerEmbedding F} →
  LiteralRealGalerkinPhaseSpace F E → List Z3.FourierMode
reconstructedModes phaseSpace =
  appendPositiveNegative (positiveOrbitCoefficients phaseSpace)
  where
  appendPositiveNegative :
    List (TransverseModeCoefficient F E) → List Z3.FourierMode
  appendPositiveNegative [] = []
  appendPositiveNegative (coefficient ∷ rest) =
    coefficientMode coefficient
    ∷ reconstructedNegativeMode coefficient
    ∷ appendPositiveNegative rest
